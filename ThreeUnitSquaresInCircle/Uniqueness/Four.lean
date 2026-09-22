import ThreeUnitSquaresInCircle.Uniqueness.Angles
import ThreeUnitSquaresInCircle.Unified.Four

/-! Equality rigidity for four squares uses the actual enclosing disk, not
uniqueness of the diamond relaxation (which is false). -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Uniqueness
open Unified

lemma closed_dot_bound (S : UnitSquare) (n : Point) {p : Point}
    (hp : closedSquare S p) : |dot n (sub p S.center)| ≤ width S n := by
  rw [← frame_dot S]
  change |frameX S n*localX S p+frameY S n*localY S p| ≤ width S n
  have ha := abs_add_le (frameX S n*localX S p) (frameY S n*localY S p)
  rw [abs_mul,abs_mul] at ha
  have hx := mul_le_mul_of_nonneg_left hp.1 (abs_nonneg (frameX S n))
  have hy := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg (frameY S n))
  dsimp [width]
  linarith

lemma closed_open_disjoint (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    {p : Point} (hS : closedSquare S p) : ¬ openSquare T p := by
  obtain ⟨e⟩ := separation_exists S T hd
  intro hT
  have h₁ := (abs_le.mp (closed_dot_bound S e.normal hS)).2
  have h₂ := (abs_lt.mp (dot_open_bound_of_ne T e.nonzero hT)).1
  have hsep := e.separates
  simp only [dot_sub_right] at *
  linarith

lemma four_contact_eq {a b : ℝ} (hφ : phi a b ≤ 2) (hs : 1 ≤ a+b) :
    a=1/2 ∧ b=1/2 := by
  have he : phi a b-2=2*(a+b-1)+(a-1/2)^2+(b-1/2)^2 := by dsimp [phi]; ring
  have hx := sq_nonneg (a-1/2)
  have hy := sq_nonneg (b-1/2)
  constructor <;> nlinarith

lemma four_some_vertex (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2) :
    ∃ i, alpha (S i) o=1/2 ∧ beta (S i) o=1/2 := by
  by_contra hn
  apply four_polygon_strict_impossible S o hd
  intro i
  have hle := p4_of_phi_le (hφ i)
  have hne : ¬ 1 ≤ alpha (S i) o+beta (S i) o := by
    intro h
    exact hn ⟨i,four_contact_eq (hφ i) h⟩
  exact lt_of_not_ge hne

lemma four_no_containing (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2) :
    ∀ i, ¬ openSquare (S i) o := by
  obtain ⟨k,hka,hkb⟩ := four_some_vertex S o hd hφ
  have hclosed : closedSquare (S k) o := by
    change alpha (S k) o ≤ 1/2 ∧ beta (S k) o ≤ 1/2
    exact ⟨hka.le,hkb.le⟩
  intro i
  by_cases hi : i=k
  · subst i
    intro h
    change alpha (S k) o < 1/2 ∧ beta (S k) o < 1/2 at h
    linarith [h.1]
  · exact closed_open_disjoint (S k) (S i) (hd k i hi.symm) hclosed

/-- At radius 1/2 an exterior square contributes at least pi/2. Actual disk
containment makes the bound strict unless the diamond tangent is saturated. -/
lemma four_half_radius_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o) (hφ : phi C.a C.b ≤ 2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p}, Real.pi/4 ≤ A.halfWidth ∧
      (C.a+C.b < 1 → Real.pi/4 < A.halfWidth) := by
  have ha := C.exterior hsort hout
  have hb := C.nonneg.2
  have hsum : C.a+C.b ≤ 1 := p4_of_phi_le hφ
  have ha' : C.a < 5/6 := by
    dsimp [phi] at hφ
    by_contra hn
    have hCa : 5/6 ≤ C.a := le_of_not_gt hn
    nlinarith [sq_nonneg (C.a-5/6),sq_nonneg C.b]
  let u := 2*C.a-1
  let v := 1-2*C.b
  let A := Real.arccos u
  let V := Real.arcsin v
  let l := max (-A) (-V)
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u < 2/3 := by dsimp [u]; linarith
  have huv : u ≤ v := by dsimp [u,v]; linarith
  have hv1 : v ≤ 1 := by dsimp [v]; linarith
  have huC : u < Real.cos (Real.pi/4) := by
    rw [Real.cos_pi_div_four]
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    have hp := Real.sqrt_nonneg 2
    nlinarith
  have hA : Real.pi/4 < A := by
    have hh := Real.arccos_lt_arccos (show -1 ≤ u by linarith) huC (Real.cos_le_one _)
    rw [Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])] at hh
    exact hh
  have hApi : A ≤ Real.pi/2 := by
    have hh := Real.arcsin_nonneg.mpr hu0
    dsimp [A,Real.arccos]; linarith
  have hB : Real.pi/2 ≤ A+V := by
    have hh := Real.arcsin_le_arcsin huv
    dsimp [A,V,Real.arccos]; linarith
  have hBs : C.a+C.b < 1 → Real.pi/2 < A+V := by
    intro hs
    have hlt : u < v := by dsimp [u,v]; linarith
    have hh := Real.arcsin_lt_arcsin (show -1 ≤ u by linarith) hlt hv1
    dsimp [A,V,Real.arccos]; linarith
  have hlen : A-l=min (2*A) (A+V) := by
    dsimp [l]
    by_cases h : A ≤ V
    · rw [max_eq_left (by linarith),min_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith),min_eq_right (by linarith)]; ring
  have hlow : Real.pi/2 ≤ A-l := by rw [hlen]; exact le_min (by linarith) hB
  have hstrict : C.a+C.b < 1 → Real.pi/2 < A-l := by
    intro hs
    rw [hlen]
    exact lt_min (by linarith) (hBs hs)
  obtain ⟨W,hW⟩ := C.arc (1/2) l A (by linarith [Real.pi_pos])
    (by have hh : -A ≤ l := le_max_left _ _; linarith [Real.pi_pos]) (by
      intro t ht
      have ht0 : -A < t := (le_max_left _ _).trans_lt ht.1
      have ht1 : t < A := ht.2
      have htpi : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) := ⟨by linarith,by linarith⟩
      have hcos : u < Real.cos t := by
        have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
          (show A ≤ Real.pi by linarith [Real.pi_pos]) (abs_lt.mpr ⟨ht0,ht1⟩)
        rw [Real.cos_arccos (by linarith) (by linarith)] at hh
        simpa only [Real.cos_abs] using hh
      have hsin : -v < Real.sin t :=
        (Real.arcsin_lt_iff_lt_sin' ⟨htpi.1,htpi.2.le⟩).mp (by
          rw [Real.arcsin_neg]
          exact (le_max_right _ _).trans_lt ht.1)
      have hsin1 : Real.sin t < 1 :=
        (Real.lt_arcsin_iff_sin_lt' ⟨htpi.1.le,htpi.2⟩).mp (by
          simpa only [Real.arcsin_one] using htpi.2)
      have hcos1 := Real.cos_le_one t
      dsimp [u,v] at hcos hsin
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
        abs_lt.mpr ⟨by linarith,by linarith⟩⟩)
  exact ⟨W,by rw [hW]; linarith,fun hs => by rw [hW]; linarith [hstrict hs]⟩

lemma four_all_vertices (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2) :
    ∀ i, alpha (S i) o=1/2 ∧ beta (S i) o=1/2 := by
  classical
  have hout := four_no_containing S o hd hφ
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  choose A hA hstrict using (fun i => four_half_radius_arc (C i) (hsort i) (hout i)
    (chart_phi (C i) (hφ i)))
  have hdisj : Pairwise (fun i j => Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hi hj => hd i j hij p ⟨hi,hj⟩)
  have htight (i : Fin 4) : 1 ≤ (C i).a+(C i).b := by
    by_contra hn
    exact uniform_arc_excess (n := 4) (by decide) A hdisj hA
      ⟨i,hstrict i (lt_of_not_ge hn)⟩
  intro i
  have hc := four_contact_eq (chart_phi (C i) (hφ i)) (htight i)
  rcases (C i).coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> constructor <;> linarith [hc.1,hc.2]

def vertexMid {S : UnitSquare} {o : Point} (C : SquareChart S o) : Direction :=
  chartAngle C.phase C.reversed (Real.pi/4)

lemma vertex_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=1/2) :
    ∃ A : OpenArc o (1/2) {p | openSquare S p},
      A.halfWidth=Real.pi/4 ∧ A.center=vertexMid C := by
  obtain ⟨A,hA,hc⟩ := chart_interval_arc C (1/2) 0 (Real.pi/2)
    (by positivity) (by linarith [Real.pi_pos]) (by
      intro t ht
      have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos])
      have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
      rw [ha,hb]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith,by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,by rw [hA]; ring,by simpa only [zero_add,div_div] using hc⟩

lemma vertex_represents {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=1/2) :
    Represents S o (vertexMid C-((Real.pi/4:ℝ):Direction)) (1/2,1/2) := by
  have h := chart_represents C
  cases hr : C.reversed
  · have he : vertexMid C-((Real.pi/4:ℝ):Direction)=C.phase := by
      simp [vertexMid,chartAngle,hr]
    simpa only [he,ha,SquareChart.signedB,hr,Bool.false_eq_true,ite_false,hb] using h
  · have hhalf : ((Real.pi/4:ℝ):Direction)+((Real.pi/4:ℝ):Direction)=((Real.pi/2:ℝ):Direction) := by
      rw [← Real.Angle.coe_add]; congr 1; ring
    have he : C.phase=(vertexMid C-((Real.pi/4:ℝ):Direction))+quarterShift 1 := by
      simp only [vertexMid,chartAngle,hr,ite_true,Real.Angle.coe_neg,quarterShift]
      rw [← hhalf]
      abel
    have h' : Represents S o
        ((vertexMid C-((Real.pi/4:ℝ):Direction))+quarterShift 1) (1/2,-1/2) := by
      simpa only [← he,ha,SquareChart.signedB,hr,ite_true,hb] using h
    simpa only [turnPoint,neg_neg] using represents_quarter 1 h'

/-- The only radius-sqrt(2) packing is the block, including the disk center. -/
theorem four_uniqueness (S : Fin 4 → UnitSquare) (o : Point)
    (hp : PackingN S o (Real.sqrt 2)) : HasNormalForm S o fourCenters := by
  classical
  have hφ (i : Fin 4) : phi (alpha (S i) o) (beta (S i) o) ≤ 2 := by
    have h := hp.phi_le i
    rwa [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)] at h
  have hvertices := four_all_vertices S o hp.disjoint hφ
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hcoords (i : Fin 4) : (C i).a=1/2 ∧ (C i).b=1/2 := by
    rcases (C i).coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
      constructor <;> linarith [(hvertices i).1,(hvertices i).2]
  choose A hA hmid using (fun i => vertex_arc (C i) (hcoords i).1 (hcoords i).2)
  have hsep (i j : Fin 4) (hij : i ≠ j) :
      Real.pi/2 ≤ dist (vertexMid (C i)) (vertexMid (C j)) := by
    have hd := (A i).centers_separated (A j)
      (Set.disjoint_left.mpr (fun p hi hj => hp.disjoint i j hij p ⟨hi,hj⟩))
    rw [hA i,hA j,hmid i,hmid j] at hd
    linarith
  have hgrid := four_directions_grid (fun i => vertexMid (C i)) hsep
  let φ := vertexMid (C 0)-((Real.pi/4:ℝ):Direction)
  apply normal_form_of_slots (φ := φ) hp.disjoint
  intro i
  obtain ⟨k,hk⟩ := hgrid i
  have hrep := vertex_represents (C i) (hcoords i).1 (hcoords i).2
  have he : vertexMid (C i)-((Real.pi/4:ℝ):Direction)=φ+quarterShift k := by
    rw [hk]; dsimp [φ]; abel
  rw [he] at hrep
  refine ⟨k,?_⟩
  have h := represents_quarter k hrep
  have hc : turnPoint k (1/2,1/2)=fourCenters k := by fin_cases k <;> norm_num [turnPoint,fourCenters]
  simpa only [hc] using h

end ThreeUnitSquaresInCircle.Uniqueness
