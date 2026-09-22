import ThreeUnitSquaresInCircle.Uniqueness.Angles
import ThreeUnitSquaresInCircle.Unified.ThreeContaining

/-! Closed exterior constraints with a strictly interior central square.
Strictness is retained at the central tangent; it is not silently assumed for
an optimal exterior square. The deficit is allowed to be zero. -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Uniqueness
open Unified

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
  have hle := (Real.le_arcsin_iff_sin_le' hdom).mpr (hsin.trans (by linarith))
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

lemma cap_length_identity_copy (A V : ℝ) : A-max (-A) (-V)=min (2*A) (A+V) := by
  by_cases h : A ≤ V
  · rw [max_eq_left (by linarith),min_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),min_eq_right (by linarith)]
    ring

lemma three_cap_arc_formula_closed {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3 C.a C.b) :
    ∃ B : OpenArc o auxThree {z | openSquare S z},
      2*B.halfWidth=threeCapLength C.a C.b := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data_closed ha C.nonneg.2 hp
  have hlen := cap_length_identity_copy (threeCapA C.a) (threeCapV C.b)
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

end ThreeUnitSquaresInCircle.Uniqueness
