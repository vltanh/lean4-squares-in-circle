import SquaresInCircles.Three.Optimality
import SquaresInCircles.Common.Angles

/-!
# Uniqueness of the T

At the optimal radius no square contains the disk centre, and the three
exterior arcs are each exactly 120 degrees. Equality leaves two contact types
for a square; one A-square and two B-squares are the only possibility, and they
are reconstructed into the T for every labelling and chart orientation.
-/
noncomputable section
open Set
namespace SquaresInCircles

/-! ## Closed constraints

At the optimal radius the exterior squares satisfy only the closed 16-gon, and
the deficit may be zero. A square containing the disk centre still has strict
tangents, which keeps the compensation argument strict. -/

lemma tangent_strict_of_ne {a b u v K : ℝ}
    (h : phi a b ≤ K) (hc : phi u v=K) (hne : a ≠ u ∨ b ≠ v) :
    2*(u+1/2)*(a-u)+2*(v+1/2)*(b-v) < 0 := by
  have he := tangent_identity a b u v
  have hpos : 0 < (a-u)^2+(b-v)^2 := by
    rcases hne with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr h))
  linarith

lemma p3_strict_of_inside {a b : ℝ} (ha : a < 1/2) (hb : b < 1/2)
    (hφ : phi a b ≤ (425:ℝ)/256) : P3Strict a b := by
  have h₀ := tangent_strict_of_ne (u := 1/2) (v := 5/16) hφ
    (by norm_num [phi]) (Or.inl (ne_of_lt ha))
  have h₁ := tangent_strict_of_ne (u := 5/16) (v := 1/2) hφ
    (by norm_num [phi]) (Or.inr (ne_of_lt hb))
  have h₂ := tangent_strict_of_ne (u := 11/16) (v := 0) hφ
    (by norm_num [phi]) (Or.inl (by linarith))
  have h₃ := tangent_strict_of_ne (u := 0) (v := 11/16) hφ
    (by norm_num [phi]) (Or.inr (by linarith))
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma asin_le_sixth {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) :
    Real.arcsin u ≤ Real.pi/6 := by
  apply (Real.arcsin_le_iff_le_sin ⟨by linarith,by linarith⟩
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).mpr
  simpa only [Real.sin_pi_div_six] using hu1

lemma truncated_closed {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hv : 1/2+(16/13)*u ≤ v) :
    2*Real.pi/3 ≤ Real.arccos u+Real.arcsin v ∧
      (Real.arccos u+Real.arcsin v ≤ 2*Real.pi/3 → u=0 ∧ v=1/2) := by
  have hA := asin_le_sixth hu0 hu1
  have hA0 := Real.arcsin_nonneg.mpr hu0
  have hsin : Real.sin (Real.arcsin u+Real.pi/6) ≤ 1/2+u := by
    rw [Real.sin_add,Real.sin_arcsin (by linarith) (by linarith),Real.sin_pi_div_six]
    have hp := mul_nonneg hu0 (sub_nonneg.mpr (Real.cos_le_one (Real.pi/6)))
    nlinarith [Real.cos_le_one (Real.arcsin u)]
  have hdom : Real.arcsin u+Real.pi/6 ∈ Ioc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  have hle := (Real.le_arcsin_iff_sin_le' (y := v) hdom).mpr (hsin.trans (by linarith))
  refine ⟨by dsimp [Real.arccos]; linarith,?_⟩
  intro hbudget
  have hu : u=0 := by
    by_contra hn
    have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hn)
    have hlt : Real.sin (Real.arcsin u+Real.pi/6) < v := hsin.trans_lt (by linarith)
    have hh := (Real.lt_arcsin_iff_sin_lt'
      ⟨hdom.1.le,by linarith [Real.pi_pos]⟩).mpr hlt
    dsimp [Real.arccos] at hbudget
    linarith
  subst u
  have he : Real.arcsin v=Real.pi/6 := by
    simp only [Real.arccos_zero,Real.arcsin_zero] at hbudget hle
    linarith
  have hv' := (Real.arcsin_eq_iff_eq_sin
    (show Real.pi/6 ∈ Ioo (-(Real.pi/2)) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])).mp he
  exact ⟨rfl,by simpa only [Real.sin_pi_div_six] using hv'⟩

lemma three_cap_data_closed {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3 a b) :
    0 ≤ (a-1/2)/auxThree ∧ (a-1/2)/auxThree ≤ 1/2 ∧
    1/2+(16/13)*((a-1/2)/auxThree) ≤ (1/2-b)/auxThree ∧
    Real.pi/3 ≤ threeCapA a ∧ threeCapA a ≤ Real.pi/2 ∧
    2*Real.pi/3 ≤ threeCapLength a b := by
  have hx0 : 0 ≤ (a-1/2)/auxThree := by dsimp [auxThree]; linarith
  have hx1 : (a-1/2)/auxThree ≤ 1/2 := by dsimp [auxThree]; linarith [hp.2.2.1]
  have hv : 1/2+(16/13)*((a-1/2)/auxThree) ≤ (1/2-b)/auxThree := by
    dsimp [auxThree]; linarith [hp.1]
  have hAsmall := asin_le_sixth hx0 hx1
  have hA0 := Real.arcsin_nonneg.mpr hx0
  have hA : Real.pi/3 ≤ threeCapA a := by dsimp [threeCapA,Real.arccos]; linarith
  have hAp : threeCapA a ≤ Real.pi/2 := by dsimp [threeCapA,Real.arccos]; linarith
  have hB := (truncated_closed hx0 hx1 hv).1
  exact ⟨hx0,hx1,hv,hA,hAp,le_min (by linarith) hB⟩

/-- Equality in the exterior arc bound identifies exactly the two contact types. -/
lemma three_cap_contact_types {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3 a b) (hlen : threeCapLength a b ≤ 2*Real.pi/3) :
    (a=11/16 ∧ b=0) ∨ (a=1/2 ∧ b=5/16) := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data_closed ha hb hp
  by_cases h : 2*threeCapA a ≤ threeCapA a+threeCapV b
  · have he : threeCapA a=Real.pi/3 := by
      rw [threeCapLength,min_eq_left h] at hlen
      linarith
    have hu := Real.cos_arccos (show -1 ≤ (a-1/2)/auxThree by linarith)
      (show (a-1/2)/auxThree ≤ 1 by linarith)
    change Real.cos (threeCapA a)=(a-1/2)/auxThree at hu
    rw [he,Real.cos_pi_div_three] at hu
    have ha' : a=11/16 := by dsimp [auxThree] at hu; linarith
    exact Or.inl ⟨ha',by linarith [hp.2.2.1]⟩
  · rw [threeCapLength,min_eq_right (by linarith)] at hlen
    obtain ⟨hu,hv'⟩ := (truncated_closed hx0 hx1 hv).2 hlen
    dsimp [auxThree] at hu hv'
    exact Or.inr ⟨by linarith,by linarith⟩

lemma compensation_closed {P Q u v : ℝ}
    (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < (16/13)*P+Q) (hPu : P ≤ u)
    (hv : 1/2+(16/13)*u ≤ v) (hv1 : v < 1) :
    4*Real.pi/3 <
      (Real.pi/2-Real.arcsin u+Real.arcsin v)+
      (Real.pi/2+Real.arcsin P+Real.arcsin Q) := by
  have htop : 1/2+(16/13)*u < 1 := hv.trans_lt hv1
  have hu : u < 1/2 := by linarith
  have hinc := three_asin_increment_mono hP hPu hu htop
  have hvmono := Real.arcsin_le_arcsin hv
  have htP : 1/2+(16/13)*P ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hpair := arcsin_sum_gt_of_sin_lt htP hQ
    (show Real.pi/6 ∈ Icc (0:ℝ) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (by rw [Real.sin_pi_div_six]; linarith)
  linarith

lemma deficit_closed {a b : ℝ} (hba : b ≤ a) (ha1 : a < 1/2) (hp : P3Strict a b)
    (hlen : threeContainingLength a b ≤ 2*Real.pi/3) :
    let P := (1/2-a)/auxThree
    let Q := (1/2-b)/auxThree
    0 < P ∧ P ≤ Q ∧ Q < 1 ∧ 1/2 < (16/13)*P+Q ∧
      Real.pi/6-Real.arcsin P-Real.arcsin Q < 1/12 := by
  dsimp only
  let P := (1/2-a)/auxThree
  let Q := (1/2-b)/auxThree
  have hP : 0 < P := by dsimp [P,auxThree]; linarith
  have hPQ : P ≤ Q := by dsimp [P,Q,auxThree]; linarith
  have hQ : 0 < Q := hP.trans_le hPQ
  have hQ1 : Q < 1 := by
    apply Real.arcsin_lt_pi_div_two.mp
    change Real.pi/2+Real.arcsin P+Real.arcsin Q ≤ 2*Real.pi/3 at hlen
    have hh := Real.arcsin_pos.mpr hP
    linarith [Real.pi_pos]
  have hcentral : 1/2 < (16/13)*P+Q := by dsimp [P,Q,auxThree]; linarith [hp.1]
  have hsum : 13/29 < P+Q := by dsimp [P,Q,auxThree]; linarith [hp.1,hp.2.1]
  have hAP := arcsin_ge_self hP.le (hPQ.trans hQ1.le)
  have hAQ := arcsin_ge_self hQ.le hQ1.le
  exact ⟨hP,hPQ,hQ1,hcentral,by linarith [pi_lt_22_over_7]⟩

lemma three_cap_mem_closed {a b t : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3 a b)
    (ht : t ∈ Ioo (max (-threeCapA a) (-threeCapV b)) (threeCapA a)) :
    |auxThree*Real.cos t-a| < 1/2 ∧ |auxThree*Real.sin t-b| < 1/2 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data_closed ha hb hp
  have ht0 : -threeCapA a < t := (le_max_left _ _).trans_lt ht.1
  have ht1 : t < threeCapA a := ht.2
  have htdom : t ∈ Ioo (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith,by linarith⟩
  have hcos : (a-1/2)/auxThree < Real.cos t := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
      (show threeCapA a ≤ Real.pi by linarith [Real.pi_pos])
      (abs_lt.mpr ⟨ht0,ht1⟩)
    rw [threeCapA,Real.cos_arccos (by linarith) (by linarith)] at h
    simpa only [Real.cos_abs] using h
  have hasin : Real.arcsin (-((1/2-b)/auxThree)) < t := by
    rw [Real.arcsin_neg]
    exact (le_max_right _ _).trans_lt ht.1
  have hsin := (Real.arcsin_lt_iff_lt_sin' ⟨htdom.1,htdom.2.le⟩).mp hasin
  have hcos1 := Real.cos_le_one t
  have hsin1 := Real.sin_le_one t
  dsimp [auxThree] at hcos hsin ⊢
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma three_cap_arc_formula_closed {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3 C.a C.b) :
    ∃ B : OpenArc o auxThree {z | openSquare S z},
      2*B.halfWidth=threeCapLength C.a C.b := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data_closed ha C.nonneg.2 hp
  have hlen := cap_length_identity (threeCapA C.a) (threeCapV C.b)
  change threeCapA C.a-max (-threeCapA C.a) (-threeCapV C.b)=
    threeCapLength C.a C.b at hlen
  obtain ⟨B,hB⟩ := C.arc auxThree
    (max (-threeCapA C.a) (-threeCapV C.b)) (threeCapA C.a)
    (by linarith [Real.pi_pos])
    (by have h := le_max_left (-threeCapA C.a) (-threeCapV C.b)
        linarith [Real.pi_pos])
    (fun t ht => three_cap_mem_closed ha C.nonneg.2 hp ht)
  exact ⟨B,by rw [hB]; linarith⟩


lemma three_gap_from_containing_closed {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hCsort : C.b ≤ C.a) (ho : openSquare S o)
    (hDa : 1/2 ≤ D.a) (hDp : P3 D.a D.b)
    (hd : Disjoint {z | openSquare S z} {z | openSquare T z}) :
    1/2-C.a ≤ D.a-1/2 := by
  by_contra hn
  have hxlt : D.a-1/2 < 1/2-C.a := lt_of_not_ge hn
  have hc := C.origin.mp ho
  have hdb : D.b < 1/2 := by
    have hsum := (p3_coordinates D.nonneg.1 D.nonneg.2 hDp).2.2
    linarith
  let t := ((D.a-1/2)+(1/2-C.a))/2
  have ht0 : 0 < t := by dsimp [t]; linarith [hc.1]
  have htx : D.a-1/2 < t := by dsimp [t]; linarith
  have htp : t < 1/2-C.a := by dsimp [t]; linarith
  have ht1 : t < 1/2 := by linarith [C.nonneg.1]
  let z := pointInDirection o D.phase t 0
  have hzT : openSquare T z := by
    apply (D.cartesian t 0).mpr
    refine ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,?_⟩
    simpa only [zero_sub,abs_neg,D.abs_signedB] using hdb
  have hα : alpha S o ≤ C.a := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> linarith
  have hβ : beta S o ≤ C.a := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> linarith
  have hzS : openSquare S z := by
    apply inscribed_disk_mem S o (a := C.a) (p := 1/2-C.a)
      (by linarith [hc.1]) (by ring) hα hβ
    rw [show z=pointInDirection o D.phase t 0 by rfl,pointInDirection_norm]
    nlinarith
  exact Set.disjoint_left.mp hd hzS hzT


lemma three_cap_reduction_closed {a b P Q L δ : ℝ}
    (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3 a b)
    (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < (16/13)*P+Q) (hgap : P ≤ (a-1/2)/auxThree)
    (hL : L=Real.pi/2+Real.arcsin P+Real.arcsin Q)
    (hδ : δ=2*Real.pi/3-L) (hδsmall : δ < 1/12)
    (hbudget : threeCapLength a b+L ≤ 4*Real.pi/3) :
    threeCapA a ≤ threeCapV b ∧ b < 1/16 ∧ a ≤ 11/16 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hmin⟩ := three_cap_data_closed ha hb hp
  have hfull : threeCapA a ≤ threeCapV b := by
    by_contra hn
    have hclip : threeCapV b < threeCapA a := lt_of_not_ge hn
    have hv1 : (1/2-b)/auxThree < 1 :=
      Real.arcsin_lt_pi_div_two.mp (hclip.trans_le hAp)
    have hcomp := compensation_closed hP hQ hcentral hgap hv hv1
    rw [threeCapLength,min_eq_right (by linarith),hL] at hbudget
    dsimp [threeCapA,threeCapV,Real.arccos] at hbudget
    linarith
  have hlen : threeCapLength a b=2*threeCapA a := min_eq_left (by linarith)
  have hnear : threeCapA a < Real.pi/3+1/24 := by rw [hlen] at hbudget; linarith
  have hrad : 9/20 < (a-1/2)/auxThree := by
    rcases eq_or_lt_of_le hx1 with he | hlt
    · rw [he]; norm_num
    · exact three_cap_near_axis hx0 hlt hnear
  dsimp [auxThree] at hrad
  exact ⟨hfull,by linarith [hp.2.2.1],by linarith [hp.2.2.1]⟩

def threeFullCapClosed {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3 C.a C.b) (hfull : threeCapA C.a ≤ threeCapV C.b) :
    OpenArc o auxThree {z | openSquare S z} :=
  symmetricChartArc C auxThree (threeCapA C.a)
    (lt_of_lt_of_le (by positivity) (three_cap_data_closed ha C.nonneg.2 hp).2.2.2.1)
    ((three_cap_data_closed ha C.nonneg.2 hp).2.2.2.2.1.trans (by linarith [Real.pi_pos]))
    (fun t ht => three_cap_mem_closed ha C.nonneg.2 hp
      (by rw [max_eq_left (by linarith)]; exact ht))

/-- Mixed boundary lemma: only the containing square needs strict tangents. -/
theorem three_containing_closed_impossible (S T U : UnitSquare) (o : Point)
    (hST : Disjoint {z | openSquare S z} {z | openSquare T z})
    (hSU : Disjoint {z | openSquare S z} {z | openSquare U z})
    (hTU : Disjoint {z | openSquare T z} {z | openSquare U z})
    (hS : P3Strict (alpha S o) (beta S o))
    (hT : P3 (alpha T o) (beta T o)) (hU : P3 (alpha U o) (beta U o))
    (ho : openSquare S o) : False := by
  obtain ⟨C,hCsort⟩ := sorted_square_chart S o
  obtain ⟨D,hDsort⟩ := sorted_square_chart T o
  obtain ⟨E,hEsort⟩ := sorted_square_chart U o
  have hpC := C.p3Strict hS
  have hpD := p3_chart D hT
  have hpE := p3_chart E hU
  have hTo : ¬ openSquare T o := fun h => Set.disjoint_left.mp hST ho h
  have hUo : ¬ openSquare U o := fun h => Set.disjoint_left.mp hSU ho h
  have hDa := D.exterior hDsort hTo
  have hEa := E.exterior hEsort hUo
  have hinside := C.origin.mp ho
  obtain ⟨A,hA⟩ := three_containing_arc_formula C ho
  obtain ⟨B,hB⟩ := three_cap_arc_formula_closed D hDa hpD
  obtain ⟨G,hG⟩ := three_cap_arc_formula_closed E hEa hpE
  have hDdata := three_cap_data_closed hDa D.nonneg.2 hpD
  have hEdata := three_cap_data_closed hEa E.nonneg.2 hpE
  have hDlen := hDdata.2.2.2.2.2
  have hElen := hEdata.2.2.2.2.2
  have hbudget := triple_arc_budget A B G hST hSU hTU
  have hLsmall : threeContainingLength C.a C.b ≤ 2*Real.pi/3 := by linarith
  let P : ℝ := (1/2-C.a)/auxThree
  let Q : ℝ := (1/2-C.b)/auxThree
  let L : ℝ := threeContainingLength C.a C.b
  let δ : ℝ := 2*Real.pi/3-L
  have hL : L=Real.pi/2+Real.arcsin P+Real.arcsin Q := rfl
  have hδ : δ=2*Real.pi/3-L := rfl
  have hA' : 2*A.halfWidth=L := hA
  obtain ⟨hP0,hPQ,hQ1,hcentral,hδsmall0⟩ := deficit_closed hCsort hinside.1 hpC hLsmall
  change 0 < P at hP0
  change P ≤ Q at hPQ
  change Q < 1 at hQ1
  change 1/2 < (16/13)*P+Q at hcentral
  change Real.pi/6-Real.arcsin P-Real.arcsin Q < 1/12 at hδsmall0
  have hδsmall : δ < 1/12 := by linarith
  have hQ : Q ∈ Icc (0:ℝ) 1 := ⟨hP0.le.trans hPQ,hQ1.le⟩
  have hgapD := three_gap_from_containing_closed C D hCsort ho hDa hpD hST
  have hgapE := three_gap_from_containing_closed C E hCsort ho hEa hpE hSU
  have hgapD' : P ≤ (D.a-1/2)/auxThree :=
    (div_le_div_iff_of_pos_right (by norm_num [auxThree])).mpr hgapD
  have hgapE' : P ≤ (E.a-1/2)/auxThree :=
    (div_le_div_iff_of_pos_right (by norm_num [auxThree])).mpr hgapE
  have hbudD : threeCapLength D.a D.b+L ≤ 4*Real.pi/3 := by linarith
  have hbudE : threeCapLength E.a E.b+L ≤ 4*Real.pi/3 := by linarith
  obtain ⟨hDfull,hDb,hDamax⟩ := three_cap_reduction_closed hDa D.nonneg.2 hpD
    hP0.le hQ hcentral hgapD' hL hδ hδsmall hbudD
  obtain ⟨hEfull,hEb,hEamax⟩ := three_cap_reduction_closed hEa E.nonneg.2 hpE
    hP0.le hQ hcentral hgapE' hL hδ hδsmall hbudE
  let Bfull := threeFullCapClosed D hDa hpD hDfull
  let Gfull := threeFullCapClosed E hEa hpE hEfull
  have hdist := A.third_distance_bounds Bfull Gfull hST hSU hTU
  change threeCapA D.a+threeCapA E.a ≤ dist D.phase E.phase ∧
    dist D.phase E.phase ≤ 2*Real.pi-2*A.halfWidth-threeCapA D.a-threeCapA E.a at hdist
  have hlo : 2*Real.pi/3 ≤ dist D.phase E.phase := by
    linarith [hDdata.2.2.2.1,hEdata.2.2.2.1,hdist.1]
  have hhi : dist D.phase E.phase < 2*Real.pi/3+1/12 := by
    linarith [hDdata.2.2.2.1,hEdata.2.2.2.1,hdist.2]
  obtain ⟨z,hzT,hzU⟩ := near_axis_square_overlap D E ⟨hDa,hDamax⟩ hDb
    ⟨hEa,hEamax⟩ hEb hlo hhi
  exact Set.disjoint_left.mp hTU hzT hzU

/-! ## Reconstruction of the T

The three arc midpoints form an equilateral triple and the two B-contact phases
are antipodal; no numerical angle choices are used. -/

lemma a_contact_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=11/16) (hb : C.b=0) :
    ∃ A : OpenArc o auxThree {p | openSquare S p},
      A.halfWidth=Real.pi/3 ∧ A.center=C.phase := by
  let A := symmetricChartArc C auxThree (Real.pi/3) (by positivity)
    (by linarith [Real.pi_pos]) (by
      intro t ht
      have hcos : 1/2 < Real.cos t := by
        have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
          (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) (abs_lt.mpr ht)
        rw [Real.cos_pi_div_three,Real.cos_abs] at hh
        exact hh
      rw [ha,hb]
      dsimp [auxThree]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith [Real.neg_one_le_sin t],by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,rfl,rfl⟩

lemma b_semicircle {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=5/16) :
    ∃ A : OpenArc o (1/16) {p | openSquare S p},
      A.halfWidth=Real.pi/2 ∧ A.center=C.phase := by
  let A := symmetricChartArc C (1/16) (Real.pi/2) (by positivity)
    (by linarith [Real.pi_pos]) (by
      intro t ht
      have hc := Real.cos_pos_of_mem_Ioo ht
      rw [ha,hb]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith [Real.neg_one_le_sin t],by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,rfl,rfl⟩

lemma b_contact_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=5/16) :
    ∃ A : OpenArc o auxThree {p | openSquare S p}, A.halfWidth=Real.pi/3 ∧
      A.center=chartAngle C.phase C.reversed (Real.pi/6) := by
  obtain ⟨A,hA,hc⟩ := chart_interval_arc C auxThree (-Real.pi/6) (Real.pi/2)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by
      intro t ht
      have hcos := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
      have hsin := Real.strictMonoOn_sin
        (show -Real.pi/6 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
        (show t ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [ht.1,ht.2,Real.pi_pos]) ht.1
      rw [neg_div,Real.sin_neg,Real.sin_pi_div_six] at hsin
      rw [ha,hb]
      dsimp [auxThree]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith,by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,by rw [hA]; ring,by convert hc using 2; ring⟩

lemma equilateral_arc_centers {o : Point} {r : ℝ} {U V W : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (G : OpenArc o r W)
    (ha : A.halfWidth=Real.pi/3) (hb : B.halfWidth=Real.pi/3) (hg : G.halfWidth=Real.pi/3)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    dist A.center B.center=2*Real.pi/3 ∧
    dist A.center G.center=2*Real.pi/3 ∧
    dist B.center G.center=2*Real.pi/3 := by
  have h₁ := A.centers_separated B hUV
  have h₂ := A.centers_separated G hUW
  have h₃ := B.centers_separated G hVW
  have hp := direction_triangle_perimeter A.center B.center G.center
  rw [dist_comm G.center A.center] at hp
  rw [ha,hb] at h₁
  rw [ha,hg] at h₂
  rw [hb,hg] at h₃
  exact ⟨by linarith,by linarith,by linarith⟩

lemma two_a_contacts_impossible {S T U : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hc : C.a=11/16 ∧ C.b=0) (hd : D.a=11/16 ∧ D.b=0)
    (G : OpenArc o auxThree {p | openSquare U p}) (hg : Real.pi/3 ≤ G.halfWidth)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (hSU : Disjoint {p | openSquare S p} {p | openSquare U p})
    (hTU : Disjoint {p | openSquare T p} {p | openSquare U p}) : False := by
  obtain ⟨A,ha,hac⟩ := a_contact_arc C hc.1 hc.2
  obtain ⟨B,hb,hbc⟩ := a_contact_arc D hd.1 hd.2
  have hdist := G.third_distance_bounds A B hSU.symm hTU.symm hST
  rw [ha,hb,hac,hbc] at hdist
  obtain ⟨p,hpS,hpT⟩ := near_axis_square_overlap C D
    ⟨by linarith [hc.1],by linarith [hc.1]⟩ (by linarith [hc.2])
    ⟨by linarith [hd.1],by linarith [hd.1]⟩ (by linarith [hd.2])
    (by linarith [hdist.1]) (by linarith [hdist.2])
  exact Set.disjoint_left.mp hST hpS hpT

lemma three_b_contacts_impossible {S T U : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) (E : SquareChart U o)
    (hc : C.a=1/2 ∧ C.b=5/16) (hd : D.a=1/2 ∧ D.b=5/16)
    (he : E.a=1/2 ∧ E.b=5/16)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (hSU : Disjoint {p | openSquare S p} {p | openSquare U p})
    (hTU : Disjoint {p | openSquare T p} {p | openSquare U p}) : False := by
  obtain ⟨A,ha,_⟩ := b_semicircle C hc.1 hc.2
  obtain ⟨B,hb,_⟩ := b_semicircle D hd.1 hd.2
  obtain ⟨G,hg,_⟩ := b_semicircle E he.1 he.2
  have h := triple_arc_budget A B G hST hSU hTU
  rw [ha,hb,hg] at h
  linarith [Real.pi_pos]

/-- Trigonometric reconstruction of the radial phase of the remaining A-square. -/
lemma apex_phase {φ ψ χ : Direction} (r s : Bool)
    (hanti : ψ=φ+(Real.pi:Direction))
    (h01 : (chartAngle ψ s (Real.pi/6)-chartAngle φ r (Real.pi/6)).cos= -(1/2))
    (h02 : (χ-chartAngle φ r (Real.pi/6)).cos= -(1/2))
    (h12 : (χ-chartAngle ψ s (Real.pi/6)).cos= -(1/2)) :
    s= !r ∧ (χ-φ).cos=0 ∧ (χ-φ).sin=(if r then 1 else -1) := by
  let δ := χ-φ
  let p : Direction := ((Real.pi/6:ℝ):Direction)
  have hcp : p.cos=Real.sqrt 3/2 := by simp [p,Real.cos_pi_div_six]
  have hsp : p.sin=(1/2:ℝ) := by simp [p,Real.sin_pi_div_six]
  cases r <;> cases s
  · have he : chartAngle ψ false (Real.pi/6)-chartAngle φ false (Real.pi/6)=(Real.pi:Direction) := by
      rw [hanti]; simp only [chartAngle,Bool.false_eq_true,ite_false]; abel
    rw [he,Real.Angle.cos_coe,Real.cos_pi] at h01
    norm_num at h01
  · have he₀ : χ-chartAngle φ false (Real.pi/6)=δ-p := by
      simp only [δ,p,chartAngle,Bool.false_eq_true,ite_false]; abel
    have he₁ : χ-chartAngle ψ true (Real.pi/6)=δ-(Real.pi:Direction)+p := by
      rw [hanti]; simp only [δ,p,chartAngle,ite_true,Real.Angle.coe_neg]; abel
    rw [he₀] at h02
    rw [he₁] at h12
    simp only [sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_neg,
      Real.Angle.sin_neg,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi,Real.sin_pi,
      hcp,hsp] at h02 h12
    have hs : δ.sin= -1 := by nlinarith
    have hc : δ.cos=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq δ]
    exact ⟨rfl,hc,hs⟩
  · have he₀ : χ-chartAngle φ true (Real.pi/6)=δ+p := by
      simp only [δ,p,chartAngle,ite_true,Real.Angle.coe_neg]; abel
    have he₁ : χ-chartAngle ψ false (Real.pi/6)=δ-(Real.pi:Direction)-p := by
      rw [hanti]; simp only [δ,p,chartAngle,Bool.false_eq_true,ite_false]; abel
    rw [he₀] at h02
    rw [he₁] at h12
    simp only [sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_neg,
      Real.Angle.sin_neg,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi,Real.sin_pi,
      hcp,hsp] at h02 h12
    have hs : δ.sin=1 := by nlinarith
    have hc : δ.cos=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq δ]
    exact ⟨rfl,hc,hs⟩
  · have he : chartAngle ψ true (Real.pi/6)-chartAngle φ true (Real.pi/6)=(Real.pi:Direction) := by
      rw [hanti]; simp only [chartAngle,ite_true]; abel
    rw [he,Real.Angle.cos_coe,Real.cos_pi] at h01
    norm_num at h01

/-- Two B-contacts and one A-contact reconstruct the T in a single frame. -/
lemma t_contact_reconstruction {S T U : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) (E : SquareChart U o)
    (hc : C.a=1/2 ∧ C.b=5/16) (hd : D.a=1/2 ∧ D.b=5/16)
    (he : E.a=11/16 ∧ E.b=0)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (hSU : Disjoint {p | openSquare S p} {p | openSquare U p})
    (hTU : Disjoint {p | openSquare T p} {p | openSquare U p}) :
    ∃ φ : Direction,
      ((Represents S o φ (Three.centers 0) ∧ Represents T o φ (Three.centers 1)) ∨
       (Represents S o φ (Three.centers 1) ∧ Represents T o φ (Three.centers 0))) ∧
      Represents U o φ (Three.centers 2) := by
  obtain ⟨A,ha,hac⟩ := b_contact_arc C hc.1 hc.2
  obtain ⟨B,hb,hbc⟩ := b_contact_arc D hd.1 hd.2
  obtain ⟨G,hg,hgc⟩ := a_contact_arc E he.1 he.2
  have hdist := equilateral_arc_centers A B G ha hb hg hST hSU hTU
  rw [hac,hbc,hgc] at hdist
  obtain ⟨A',ha',hac'⟩ := b_semicircle C hc.1 hc.2
  obtain ⟨B',hb',hbc'⟩ := b_semicircle D hd.1 hd.2
  have hanti : D.phase=C.phase+(Real.pi:Direction) := by
    apply antipodal_of_distance
    have hh := A'.centers_separated B' hST
    rw [ha',hb',hac',hbc'] at hh
    have hu := direction_diameter C.phase D.phase
    linarith
  have h01 := cos_sub_distance (chartAngle C.phase C.reversed (Real.pi/6))
    (chartAngle D.phase D.reversed (Real.pi/6))
  have h02 := cos_sub_distance (chartAngle C.phase C.reversed (Real.pi/6)) E.phase
  have h12 := cos_sub_distance (chartAngle D.phase D.reversed (Real.pi/6)) E.phase
  rw [hdist.1,cos_two_pi_thirds] at h01
  rw [hdist.2.1,cos_two_pi_thirds] at h02
  rw [hdist.2.2,cos_two_pi_thirds] at h12
  obtain ⟨hrev,hEcos,hEsin⟩ := apex_phase C.reversed D.reversed hanti h01 h02 h12
  have hC := chart_represents C
  have hD := chart_represents D
  have hE := chart_represents E
  cases hr : C.reversed
  · have hrD : D.reversed=true := by simpa only [hr,Bool.not_false] using hrev
    let φ := C.phase+(Real.pi:Direction)
    have hCc : (C.phase-φ).cos= -1 := by
      have hh : C.phase-φ= -(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh]; simp
    have hCs : (C.phase-φ).sin=0 := by
      have hh : C.phase-φ= -(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh]; simp
    have hDφ : D.phase=φ := hanti
    have hEc : (E.phase-φ).cos=0 := by
      have hh : E.phase-φ=(E.phase-C.phase)-(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh,Real.Angle.cos_sub_pi,hEcos]; ring
    have hEs : (E.phase-φ).sin=1 := by
      have hh : E.phase-φ=(E.phase-C.phase)-(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh,Real.Angle.sin_sub_pi]
      simpa only [hr,Bool.false_eq_true,ite_false,neg_neg] using congrArg Neg.neg hEsin
    have rC := represents_cardinal (ψ := φ) hC 2 (by simpa [quarterShift] using hCc)
      (by simpa [quarterShift] using hCs)
    have rD := represents_cardinal (ψ := φ) hD 0 (by simp [hDφ,quarterShift]) (by simp [hDφ,quarterShift])
    have rE := represents_cardinal (ψ := φ) hE 1 (by simpa [quarterShift] using hEc)
      (by simpa [quarterShift] using hEs)
    refine ⟨φ,Or.inl ⟨?_,?_⟩,?_⟩
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,hr,hc.1,hc.2] using rC
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,hrD,hd.1,hd.2] using rD
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,he.1,he.2] using rE
  · have hrD : D.reversed=false := by simpa only [hr,Bool.not_true] using hrev
    let φ := C.phase
    have rC : Represents S o φ (Three.centers 1) := by
      simpa [neg_div,φ,Three.centers,SquareChart.signedB,hr,hc.1,hc.2] using hC
    have rD := represents_cardinal (ψ := φ) hD 2
      (by simp [φ,hanti,quarterShift]) (by simp [φ,hanti,quarterShift])
    have rE := represents_cardinal (ψ := φ) hE 1
      (by simpa [φ,quarterShift] using hEcos)
      (by simpa [φ,quarterShift,hr] using hEsin)
    refine ⟨φ,Or.inr ⟨rC,?_⟩,?_⟩
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,hrD,hd.1,hd.2] using rD
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,he.1,he.2] using rE

/-! ## Assembly -/

lemma three_no_containing (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ (425:ℝ)/256) :
    ∀ i, ¬ openSquare (S i) o := by
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p} :=
    Set.disjoint_left.mpr (fun p hi hj => hd i j hij p ⟨hi,hj⟩)
  have hclosed (i : Fin 3) := p3_of_phi_le (hφ i)
  intro i hi
  have hstrict : P3Strict (alpha (S i) o) (beta (S i) o) :=
    p3_strict_of_inside hi.1 hi.2 (hφ i)
  fin_cases i
  · exact three_containing_closed_impossible (S 0) (S 1) (S 2) o
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
      hstrict (hclosed 1) (hclosed 2) hi
  · exact three_containing_closed_impossible (S 1) (S 0) (S 2) o
      (hpair 1 0 (by decide)) (hpair 1 2 (by decide)) (hpair 0 2 (by decide))
      hstrict (hclosed 0) (hclosed 2) hi
  · exact three_containing_closed_impossible (S 2) (S 0) (S 1) o
      (hpair 2 0 (by decide)) (hpair 2 1 (by decide)) (hpair 0 1 (by decide))
      hstrict (hclosed 0) (hclosed 1) hi

lemma assemble_three {S : Fin 3 → UnitSquare} {o : Point} (hd : InteriorDisjoint S)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : ∃ φ : Direction,
      ((Represents (S i) o φ (Three.centers 0) ∧ Represents (S j) o φ (Three.centers 1)) ∨
       (Represents (S i) o φ (Three.centers 1) ∧ Represents (S j) o φ (Three.centers 0))) ∧
      Represents (S k) o φ (Three.centers 2)) : HasNormalForm S o Three.centers := by
  have hcover : ∀ l : Fin 3, l=i ∨ l=j ∨ l=k := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim | decide
  obtain ⟨φ,hij',hk⟩ := h
  apply normal_form_of_slots (φ := φ) hd
  intro l
  rcases hcover l with rfl | rfl | rfl
  · rcases hij' with h | h
    · exact ⟨0,h.1⟩
    · exact ⟨1,h.1⟩
  · rcases hij' with h | h
    · exact ⟨1,h.2⟩
    · exact ⟨0,h.2⟩
  · exact ⟨2,hk⟩

/-- Every optimal three-square packing is one rigid image of the T model. -/
theorem Three.uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o Three.radius) : HasNormalForm S o Three.centers := by
  classical
  have hφ (i : Fin 3) : phi (alpha (S i) o) (beta (S i) o) ≤ (425:ℝ)/256 := by
    have h := hp.phi_le i
    rwa [Three.radius_sq] at h
  have hout := three_no_containing S o hp.disjoint hφ
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p} :=
    Set.disjoint_left.mpr (fun p hi hj => hp.disjoint i j hij p ⟨hi,hj⟩)
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hpC (i : Fin 3) : P3 (C i).a (C i).b :=
    p3_chart (C i) (p3_of_phi_le (hφ i))
  have haC (i : Fin 3) : 1/2 ≤ (C i).a := (C i).exterior (hsort i) (hout i)
  choose A hlen using (fun i => three_cap_arc_formula_closed (C i) (haC i) (hpC i))
  have hlo (i : Fin 3) : Real.pi/3 ≤ (A i).halfWidth := by
    have hh := (three_cap_data_closed (haC i) (C i).nonneg.2 (hpC i)).2.2.2.2.2
    linarith [hlen i]
  have hbudget := open_arc_budget A (fun i j hij => hpair i j hij)
  rw [Fin.sum_univ_three] at hbudget
  have hup (i : Fin 3) : threeCapLength (C i).a (C i).b ≤ 2*Real.pi/3 := by
    have key : i=0 ∨ i=1 ∨ i=2 := by revert i; decide
    rcases key with rfl | rfl | rfl <;> linarith [hlo 0,hlo 1,hlo 2,hlen 0,hlen 1,hlen 2]
  have htype (i : Fin 3) : ((C i).a=11/16 ∧ (C i).b=0) ∨
      ((C i).a=1/2 ∧ (C i).b=5/16) :=
    three_cap_contact_types (haC i) (C i).nonneg.2 (hpC i) (hup i)
  have hnotTwo (i j : Fin 3) (hij : i ≠ j)
      (hi : (C i).a=11/16 ∧ (C i).b=0)
      (hj : (C j).a=11/16 ∧ (C j).b=0) : False := by
    have hthird : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | decide
    obtain ⟨k,hik,hjk⟩ := hthird
    exact two_a_contacts_impossible (C i) (C j) hi hj (A k) (hlo k)
      (hpair i j hij) (hpair i k hik) (hpair j k hjk)
  have hex : ∃ k : Fin 3, (C k).a=11/16 ∧ (C k).b=0 := by
    by_contra hn
    push Not at hn
    have hb (i : Fin 3) : (C i).a=1/2 ∧ (C i).b=5/16 :=
      (htype i).resolve_left (by intro h; exact hn i h.1 h.2)
    exact three_b_contacts_impossible (C 0) (C 1) (C 2) (hb 0) (hb 1) (hb 2)
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
  obtain ⟨k,hk⟩ := hex
  have hb (i : Fin 3) (hik : i ≠ k) : (C i).a=1/2 ∧ (C i).b=5/16 :=
    (htype i).resolve_left (fun hi => hnotTwo i k hik hi hk)
  fin_cases k
  · apply assemble_three hp.disjoint 1 2 0 (by decide) (by decide) (by decide)
    exact t_contact_reconstruction (C 1) (C 2) (C 0)
      (hb 1 (by decide)) (hb 2 (by decide)) hk
      (hpair 1 2 (by decide)) (hpair 1 0 (by decide)) (hpair 2 0 (by decide))
  · apply assemble_three hp.disjoint 0 2 1 (by decide) (by decide) (by decide)
    exact t_contact_reconstruction (C 0) (C 2) (C 1)
      (hb 0 (by decide)) (hb 2 (by decide)) hk
      (hpair 0 2 (by decide)) (hpair 0 1 (by decide)) (hpair 2 1 (by decide))
  · apply assemble_three hp.disjoint 0 1 2 (by decide) (by decide) (by decide)
    exact t_contact_reconstruction (C 0) (C 1) (C 2)
      (hb 0 (by decide)) (hb 1 (by decide)) hk
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))

theorem Three.rigid_uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o Three.radius) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin 3)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, closedSquare (S (σ i)) (e p) ↔ ClosedRect (Three.centers i) p.1 p.2) :=
  (Three.uniqueness S o hp).rigid_witness

end SquaresInCircles
