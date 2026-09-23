import SquaresInCircles.Three.Exterior
import SquaresInCircles.Common.Coordinates
import SquaresInCircles.Common.ArcMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The containing square, three squares

If the disk centre lies inside one square, the other two are exterior. Three
disjoint arc witnesses on the circle of radius `3/8` bound the containing
square's deficit. A clipped exterior cap would compensate for that entire
deficit. Otherwise both exterior caps are full and nearly axial, the circle
perimeter inequality pins the angle between them, and an explicit point lies in
both, contradicting interior-disjointness.
-/
noncomputable section
open Set
namespace SquaresInCircles

/-! ## Deficit and compensation estimates

The variables `P`, `Q`, `u`, `v` of the compensation lemma are normalized by
the auxiliary radius `3/8`. The only calculus step is a one-dimensional
monotonicity comparison, with explicit positive square-root denominators. -/

lemma SquareChart.p3Strict {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hp : P3Strict (alpha S o) (beta S o)) : P3Strict C.a C.b := by
  rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simpa only [ha,hb] using hp
  · rw [ha,hb]
    exact ⟨by linarith [hp.2.1],by linarith [hp.1],
      by linarith [hp.2.2.2],by linarith [hp.2.2.1]⟩

lemma three_asin_increment_mono {P u : ℝ}
    (hP : 0 ≤ P) (hPu : P ≤ u) (hu : u < 1/2)
    (htop : 1/2+(16/13)*u < 1) :
    Real.arcsin (1/2+(16/13)*P)-Real.arcsin P ≤
      Real.arcsin (1/2+(16/13)*u)-Real.arcsin u := by
  let f : ℝ → ℝ := fun t => Real.arcsin (1/2+(16/13)*t)-Real.arcsin t
  let df : ℝ → ℝ := fun t =>
    (1/Real.sqrt (1-(1/2+(16/13)*t)^2))*(16/13) -
      1/Real.sqrt (1-t^2)
  have htdata (t : ℝ) (ht : t ∈ Icc P u) :
      0 ≤ t ∧ t < 1/2 ∧ 0 < 1/2+(16/13)*t ∧ 1/2+(16/13)*t < 1 := by
    exact ⟨by linarith [ht.1],by linarith [ht.2],
      by linarith [ht.1],by linarith [ht.2]⟩
  have hder (t : ℝ) (ht : t ∈ Icc P u) : HasDerivAt f (df t) t := by
    obtain ⟨ht0,ht1,hg0,hg1⟩ := htdata t ht
    have hg : HasDerivAt (fun z : ℝ => 1/2+(16/13)*z) (16/13) t :=
      (((hasDerivAt_id' t).const_mul (16/13 : ℝ)).const_add (1/2 : ℝ)).congr_deriv
        (by ring)
    have hd := ((Real.hasDerivAt_arcsin (by linarith : 1/2+(16/13)*t ≠ -1)
      (by linarith : 1/2+(16/13)*t ≠ 1)).comp t hg).sub
        (Real.hasDerivAt_arcsin (by linarith : t ≠ -1) (by linarith : t ≠ 1))
    exact hd
  have hdf (t : ℝ) (ht : t ∈ Icc P u) : 0 ≤ df t := by
    obtain ⟨ht0,ht1,hg0,hg1⟩ := htdata t ht
    have hs0 : 0 < Real.sqrt (1-(1/2+(16/13)*t)^2) :=
      Real.sqrt_pos.mpr (by nlinarith)
    have hl0 : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.mpr (by nlinarith)
    have hsle : Real.sqrt (1-(1/2+(16/13)*t)^2) ≤ Real.sqrt (1-t^2) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have hrec := (div_le_div_iff₀ hl0 hs0).mpr
      (show 1*Real.sqrt (1-(1/2+(16/13)*t)^2) ≤ 1*Real.sqrt (1-t^2) by linarith)
    have hpos : 0 < 1/Real.sqrt (1-(1/2+(16/13)*t)^2) := one_div_pos.mpr hs0
    dsimp [df]
    linarith
  have hmono : MonotoneOn f (Icc P u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc P u)
      (show ContinuousOn f (Icc P u) by dsimp [f]; fun_prop)
    · intro t ht
      exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hder t (interior_subset ht)).deriv]
      exact hdf t (interior_subset ht)
  exact hmono ⟨le_rfl,hPu⟩ ⟨hPu,le_rfl⟩ hPu

/-- A clipped neighboring arc plus the containing arc already exceed 240 degrees. -/
lemma three_compensation {P Q u v : ℝ}
    (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < (16/13)*P+Q)
    (hPu : P ≤ u) (hu : u < 1/2)
    (hv : 1/2+(16/13)*u < v) (hv1 : v < 1) :
    4*Real.pi/3 <
      (Real.pi/2-Real.arcsin u+Real.arcsin v) +
      (Real.pi/2+Real.arcsin P+Real.arcsin Q) := by
  have htop : 1/2+(16/13)*u < 1 := hv.trans hv1
  have hinc := three_asin_increment_mono hP hPu hu htop
  have hvmono := Real.arcsin_le_arcsin hv.le
  have htP : 1/2+(16/13)*P ∈ Icc (0:ℝ) 1 :=
    ⟨by linarith,by linarith⟩
  have hpair := arcsin_sum_gt_of_sin_lt htP hQ
    (show Real.pi/6 ∈ Icc (0:ℝ) (Real.pi/2) by
      constructor <;> linarith [Real.pi_pos])
    (by rw [Real.sin_pi_div_six]; linarith)
  linarith

/-- The deficit bounds use the two first contact tangents, not numerical trig. -/
lemma three_deficit_bounds {a b : ℝ}
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hba : b ≤ a)
    (ha1 : a < 1/2) (_hb1 : b < 1/2) (hp : P3Strict a b)
    (hlen : Real.pi/2+Real.arcsin ((1/2-a)/auxThree)+
      Real.arcsin ((1/2-b)/auxThree) < 2*Real.pi/3) :
    let P := (1/2-a)/auxThree
    let Q := (1/2-b)/auxThree
    let δ := Real.pi/6-Real.arcsin P-Real.arcsin Q
    0 < P ∧ P ≤ Q ∧ Q < 1 ∧
      1/2 < (16/13)*P+Q ∧ 0 < δ ∧ δ < 1/12 := by
  dsimp only
  let P := (1/2-a)/auxThree
  let Q := (1/2-b)/auxThree
  have hP0 : 0 < P := by dsimp [P,auxThree]; linarith
  have hQ0 : 0 < Q := by dsimp [Q,auxThree]; linarith
  have hPQ : P ≤ Q := by dsimp [P,Q,auxThree]; linarith
  have hAP := Real.arcsin_pos.mpr hP0
  have hAQ := Real.arcsin_pos.mpr hQ0
  have hQ1 : Q < 1 := by
    apply Real.arcsin_lt_pi_div_two.mp
    change Real.pi/2+Real.arcsin P+Real.arcsin Q < 2*Real.pi/3 at hlen
    linarith [Real.pi_pos]
  have hP1 : P ≤ 1 := by linarith
  have hlin : 1/2 < (16/13)*P+Q := by
    dsimp [P,Q,auxThree]
    linarith [hp.1]
  have hsum : 13/29 < P+Q := by
    dsimp [P,Q,auxThree]
    linarith [hp.1,hp.2.1]
  have hlP := arcsin_ge_self hP0.le hP1
  have hlQ := arcsin_ge_self hQ0.le hQ1.le
  refine ⟨hP0,hPQ,hQ1,hlin,?_,?_⟩
  · change Real.pi/2+Real.arcsin P+Real.arcsin Q < 2*Real.pi/3 at hlen
    linarith
  · change Real.pi/6-Real.arcsin P-Real.arcsin Q < 1/12
    linarith [pi_lt_22_over_7]

/-- A cap within 1/24 radians of pi/3 has radial coordinate > 9/20. -/
lemma three_cap_near_axis {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1/2)
    (hA : Real.arccos u < Real.pi/3+1/24) : 9/20 < u := by
  have hAlow : Real.pi/3 < Real.arccos u := by
    have h := arcsin_lt_sixth hu0 hu1
    dsimp [Real.arccos]
    linarith
  let ε := Real.arccos u-Real.pi/3
  have hε0 : 0 ≤ ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/24 := by dsimp [ε]; linarith
  have hεpi : ε ≤ Real.pi := by
    dsimp [ε]
    linarith [Real.arccos_le_pi u,Real.pi_pos]
  have hsε0 := Real.sin_nonneg_of_nonneg_of_le_pi hε0 hεpi
  have hsε1 := Real.sin_le hε0
  have hcε := Real.one_sub_sq_div_two_le_cos (x := ε)
  have hmul := mul_nonneg hsε0 (sub_nonneg.mpr (Real.sin_le_one (Real.pi/3)))
  have he : u=(1/2)*Real.cos ε-Real.sin (Real.pi/3)*Real.sin ε := by
    have h := Real.cos_arccos (by linarith : -1 ≤ u) (by linarith : u ≤ 1)
    rw [show Real.arccos u=Real.pi/3+ε by dsimp [ε]; ring,
      Real.cos_add,Real.cos_pi_div_three] at h
    exact h.symm
  have hε2 : ε^2 < (1/24:ℝ)^2 := by nlinarith
  nlinarith

/-! ## Arc witnesses

The containing witness is only an interval known to lie in the square; it is
never assumed to be the entire intersection. The exterior witness has a
specified clipped-cap length; once clipping is excluded, its centre is kept. -/

def threeCapA (a : ℝ) : ℝ := Real.arccos ((a-1/2)/auxThree)
def threeCapV (b : ℝ) : ℝ := Real.arcsin ((1/2-b)/auxThree)
def threeCapLength (a b : ℝ) : ℝ :=
  min (2*threeCapA a) (threeCapA a+threeCapV b)
def threeContainingLength (a b : ℝ) : ℝ :=
  Real.pi/2+Real.arcsin ((1/2-a)/auxThree)+Real.arcsin ((1/2-b)/auxThree)

lemma three_cap_data {a b : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3Strict a b) :
    0 ≤ (a-1/2)/auxThree ∧ (a-1/2)/auxThree < 1/2 ∧
    1/2+(16/13)*((a-1/2)/auxThree) < (1/2-b)/auxThree ∧
    Real.pi/3 < threeCapA a ∧ threeCapA a ≤ Real.pi/2 ∧
    2*Real.pi/3 < threeCapLength a b := by
  have hx0 : 0 ≤ (a-1/2)/auxThree := by dsimp [auxThree]; linarith
  have hx1 : (a-1/2)/auxThree < 1/2 := by
    dsimp [auxThree]; linarith [hp.2.2.1]
  have hv : 1/2+(16/13)*((a-1/2)/auxThree) < (1/2-b)/auxThree := by
    dsimp [auxThree]; linarith [hp.1]
  have hAsmall := arcsin_lt_sixth hx0 hx1
  have hA0 := Real.arcsin_nonneg.mpr hx0
  have hA : Real.pi/3 < threeCapA a := by
    dsimp [threeCapA,Real.arccos]; linarith
  have hAp : threeCapA a ≤ Real.pi/2 := by
    dsimp [threeCapA,Real.arccos]; linarith
  have hB := three_truncated_gap hx0 hx1
    (show 1/2+(a-1/2)/auxThree < (1/2-b)/auxThree by linarith)
  refine ⟨hx0,hx1,hv,hA,hAp,?_⟩
  exact lt_min (by linarith) hB

lemma three_cap_mem {a b t : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hp : P3Strict a b)
    (ht : t ∈ Ioo (max (-threeCapA a) (-threeCapV b)) (threeCapA a)) :
    |auxThree*Real.cos t-a| < 1/2 ∧ |auxThree*Real.sin t-b| < 1/2 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data ha hb hp
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

lemma cap_length_identity (A V : ℝ) : A-max (-A) (-V)=min (2*A) (A+V) := by
  by_cases h : A ≤ V
  · rw [max_eq_left (by linarith),min_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith),min_eq_right (by linarith)]
    ring

lemma three_cap_arc_formula {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3Strict C.a C.b) :
    ∃ B : OpenArc o auxThree {z | openSquare S z},
      2*B.halfWidth=threeCapLength C.a C.b := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hgap⟩ := three_cap_data ha C.nonneg.2 hp
  have hlen := cap_length_identity (threeCapA C.a) (threeCapV C.b)
  change threeCapA C.a-max (-threeCapA C.a) (-threeCapV C.b)=
    threeCapLength C.a C.b at hlen
  obtain ⟨B,hB⟩ := C.arc auxThree
    (max (-threeCapA C.a) (-threeCapV C.b)) (threeCapA C.a)
    (by linarith [Real.pi_pos])
    (by have h := le_max_left (-threeCapA C.a) (-threeCapV C.b)
        linarith [Real.pi_pos])
    (fun t ht => three_cap_mem ha C.nonneg.2 hp ht)
  exact ⟨B,by rw [hB]; linarith⟩

lemma three_containing_mem {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a < 1/2) (hb1 : b < 1/2)
    (ht : t ∈ Ioo (-Real.arcsin ((1/2-b)/auxThree))
      (Real.pi/2+Real.arcsin ((1/2-a)/auxThree))) :
    |auxThree*Real.cos t-a| < 1/2 ∧ |auxThree*Real.sin t-b| < 1/2 := by
  have hp : 0 < (1/2-a)/auxThree := by dsimp [auxThree]; linarith
  have hq : 0 < (1/2-b)/auxThree := by dsimp [auxThree]; linarith
  have ht0 : -(Real.pi/2) < t := by
    linarith [Real.arcsin_le_pi_div_two ((1/2-b)/auxThree),ht.1]
  have ht1 : t < Real.pi := by
    linarith [Real.arcsin_le_pi_div_two ((1/2-a)/auxThree),ht.2]
  have hcos : -((1/2-a)/auxThree) < Real.cos t := by
    by_cases ht2 : t ≤ Real.pi/2
    · have hc := Real.cos_nonneg_of_mem_Icc ⟨ht0.le,ht2⟩
      linarith
    · have hdom : Real.pi/2-t ∈ Ioc (-(Real.pi/2)) (Real.pi/2) :=
        ⟨by linarith,by linarith [Real.pi_pos]⟩
      have haS : Real.arcsin (-((1/2-a)/auxThree)) < Real.pi/2-t := by
        rw [Real.arcsin_neg]
        linarith [ht.2]
      have h := (Real.arcsin_lt_iff_lt_sin' hdom).mp haS
      simpa only [Real.sin_pi_div_two_sub] using h
  have hsin : -((1/2-b)/auxThree) < Real.sin t := by
    by_cases ht2 : t ≤ Real.pi/2
    · have h := (Real.arcsin_lt_iff_lt_sin' ⟨ht0,ht2⟩).mp
        (show Real.arcsin (-((1/2-b)/auxThree)) < t by
          rw [Real.arcsin_neg]; exact ht.1)
      exact h
    · have hs := Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [Real.pi_pos]) ht1.le
      linarith
  have hc1 := Real.cos_le_one t
  have hs1 := Real.sin_le_one t
  dsimp [auxThree] at hcos hsin ⊢
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma three_containing_arc_formula {S : UnitSquare} {o : Point}
    (C : SquareChart S o) (ho : openSquare S o) :
    ∃ A : OpenArc o auxThree {z | openSquare S z},
      2*A.halfWidth=threeContainingLength C.a C.b := by
  have hc := C.origin.mp ho
  have hP0 := Real.arcsin_pos.mpr
    (show 0 < (1/2-C.a)/auxThree by dsimp [auxThree]; linarith [hc.1])
  have hQ0 := Real.arcsin_pos.mpr
    (show 0 < (1/2-C.b)/auxThree by dsimp [auxThree]; linarith [hc.2])
  obtain ⟨A,hA⟩ := C.arc auxThree
    (-Real.arcsin ((1/2-C.b)/auxThree))
    (Real.pi/2+Real.arcsin ((1/2-C.a)/auxThree))
    (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos,Real.arcsin_le_pi_div_two ((1/2-C.a)/auxThree),
      Real.arcsin_le_pi_div_two ((1/2-C.b)/auxThree)])
    (fun t ht => three_containing_mem C.nonneg.1 C.nonneg.2 hc.1 hc.2 ht)
  refine ⟨A,?_⟩
  rw [hA]
  dsimp [threeContainingLength]
  ring

/-- Disjointness from the inscribed disk forces the exterior radial gap. -/
lemma three_gap_from_containing {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hCsort : C.b ≤ C.a) (ho : openSquare S o)
    (hDa : 1/2 ≤ D.a) (hDp : P3Strict D.a D.b)
    (hd : Disjoint {z | openSquare S z} {z | openSquare T z}) :
    1/2-C.a ≤ D.a-1/2 := by
  by_contra hn
  have hxlt : D.a-1/2 < 1/2-C.a := lt_of_not_ge hn
  have hc := C.origin.mp ho
  have hdb : D.b < 1/2 := by
    have hsum := (p3_coordinates D.nonneg.1 D.nonneg.2 (p3Strict_to_p3 hDp)).2.2
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

/-- The budget excludes clipping, and forces a small transverse center coordinate. -/
lemma three_cap_reduction {a b P Q L δ : ℝ}
    (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3Strict a b)
    (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < (16/13)*P+Q)
    (hgap : P ≤ (a-1/2)/auxThree)
    (hL : L=Real.pi/2+Real.arcsin P+Real.arcsin Q)
    (hδ : δ=2*Real.pi/3-L) (hδsmall : δ < 1/12)
    (hbudget : threeCapLength a b+L < 4*Real.pi/3) :
    threeCapA a ≤ threeCapV b ∧ b < 1/16 ∧ a ≤ 11/16 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hmin⟩ := three_cap_data ha hb hp
  have hnotclip : threeCapA a ≤ threeCapV b := by
    by_contra hn
    have hclip : threeCapV b < threeCapA a := lt_of_not_ge hn
    have hv1 : (1/2-b)/auxThree < 1 := by
      apply Real.arcsin_lt_pi_div_two.mp
      exact hclip.trans_le hAp
    have hcomp := three_compensation hP hQ hcentral hgap hx1 hv hv1
    have he : threeCapLength a b=threeCapA a+threeCapV b := by
      unfold threeCapLength
      exact min_eq_right (by linarith)
    rw [he,hL] at hbudget
    dsimp [threeCapA,threeCapV,Real.arccos] at hbudget
    linarith
  have hlen : threeCapLength a b=2*threeCapA a := by
    unfold threeCapLength
    exact min_eq_left (by linarith)
  have hAnear : threeCapA a < Real.pi/3+1/24 := by
    rw [hlen] at hbudget
    linarith
  have hrad := three_cap_near_axis hx0 hx1 hAnear
  have hsmall : b < 1/16 := by
    dsimp [auxThree] at hrad
    linarith [hp.2.2.1]
  exact ⟨hnotclip,hsmall,by linarith [hp.2.2.1]⟩

/-- In the surviving alternative, a symmetric occupied cap has the actual radial phase. -/
def threeFullCap {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : 1/2 ≤ C.a) (hp : P3Strict C.a C.b)
    (hfull : threeCapA C.a ≤ threeCapV C.b) :
    OpenArc o auxThree {z | openSquare S z} :=
  symmetricChartArc C auxThree (threeCapA C.a)
    (lt_trans (by positivity) (three_cap_data ha C.nonneg.2 hp).2.2.2.1)
    (le_trans (three_cap_data ha C.nonneg.2 hp).2.2.2.2.1
      (by linarith [Real.pi_pos]))
    (fun t ht => three_cap_mem ha C.nonneg.2 hp
      (by rw [max_eq_left (by linarith)]; exact ht))

/-! ## Two nearly axial squares overlap

If two squares have small transverse chart coordinates and their radial phases
differ by between `2*pi/3` and `2*pi/3+1/12`, an explicit point lies in the
open interiors of both. -/

lemma near_axis_angles {φ ψ : Direction}
    (hlo : 2*Real.pi/3 ≤ dist φ ψ)
    (hhi : dist φ ψ < 2*Real.pi/3+1/12) :
    -(3/5:ℝ) < (ψ-φ).cos ∧ (ψ-φ).cos ≤ -1/2 ∧
      4/5 < |(ψ-φ).sin| ∧ |(ψ-φ).sin| < 7/8 := by
  let γ := |(ψ-φ).toReal|
  have hγ : γ=dist φ ψ := by rw [dist_comm,direction_dist]
  have hγpi : γ ≤ Real.pi := (ψ-φ).abs_toReal_le_pi
  have hcγ : Real.cos γ=(ψ-φ).cos := by
    have h := congrArg Real.Angle.cos (Real.Angle.coe_toReal (ψ-φ))
    simpa only [γ,Real.cos_abs,Real.Angle.cos_coe] using h
  have hcbase : Real.cos (2*Real.pi/3)=-(1/2:ℝ) := by
    rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,
      Real.cos_pi_div_three]
    norm_num
  have hcle : Real.cos γ ≤ -1/2 := by
    rcases eq_or_lt_of_le (hlo.trans_eq hγ.symm) with he | he
    · rw [← he,hcbase]; norm_num
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi
        (show 0 ≤ 2*Real.pi/3 by positivity) hγpi he
      rw [hcbase] at hh
      linarith
  let ε := γ-2*Real.pi/3
  have hε0 : 0 ≤ ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/12 := by dsimp [ε]; linarith
  have hεpi : ε ≤ Real.pi := by dsimp [ε]; linarith [Real.pi_pos]
  have hsε0 := Real.sin_nonneg_of_nonneg_of_le_pi hε0 hεpi
  have hsε1 := Real.sin_le hε0
  have hprod := mul_nonneg hsε0 (sub_nonneg.mpr (Real.sin_le_one (2*Real.pi/3)))
  have hid : Real.cos γ =
      -(1/2)*Real.cos ε-Real.sin (2*Real.pi/3)*Real.sin ε := by
    rw [show γ=2*Real.pi/3+ε by dsimp [ε]; ring,Real.cos_add,hcbase]
  have hclo : -(3/5:ℝ) < Real.cos γ := by
    nlinarith [Real.cos_le_one ε]
  rw [hcγ] at hcle hclo
  have hu := Real.Angle.cos_sq_add_sin_sq (ψ-φ)
  have hsabs := abs_nonneg (ψ-φ).sin
  have hssq : |(ψ-φ).sin|^2=(ψ-φ).sin^2 := sq_abs _
  have hcSqUp : (ψ-φ).cos^2 < (3/5:ℝ)^2 := by
    have h := mul_pos (show 0 < (ψ-φ).cos+3/5 by linarith)
      (show 0 < 3/5-(ψ-φ).cos by linarith)
    nlinarith
  have hcSqLo : (1/2:ℝ)^2 ≤ (ψ-φ).cos^2 := by
    have h := mul_nonneg (show 0 ≤ -(ψ-φ).cos-1/2 by linarith)
      (show 0 ≤ -(ψ-φ).cos+1/2 by linarith)
    nlinarith
  refine ⟨hclo,hcle,?_,?_⟩
  · by_contra hn
    have h := mul_nonneg (show 0 ≤ 4/5-|(ψ-φ).sin| by linarith)
      (show 0 ≤ 4/5+|(ψ-φ).sin| by positivity)
    nlinarith
  · by_contra hn
    have h := mul_nonneg (show 0 ≤ |(ψ-φ).sin|-7/8 by linarith)
      (show 0 ≤ |(ψ-φ).sin|+7/8 by positivity)
    nlinarith

/-- An explicit intersection point, not another separating-axis assumption. -/
lemma near_axis_square_overlap {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (ha : 1/2 ≤ C.a ∧ C.a ≤ 11/16) (hb : C.b < 1/16)
    (ha' : 1/2 ≤ D.a ∧ D.a ≤ 11/16) (hb' : D.b < 1/16)
    (hlo : 2*Real.pi/3 ≤ dist C.phase D.phase)
    (hhi : dist C.phase D.phase < 2*Real.pi/3+1/12) :
    ∃ z, openSquare S z ∧ openSquare T z := by
  obtain ⟨hc0,hc1,hs0,hs1⟩ := near_axis_angles hlo hhi
  have hbabs : |C.signedB| < 1/16 := by rw [C.abs_signedB]; exact hb
  have hbabs' : |D.signedB| < 1/16 := by rw [D.abs_signedB]; exact hb'
  rcases abs_lt.mp hbabs with ⟨hb0,hb1⟩
  rcases abs_lt.mp hbabs' with ⟨hb0',hb1'⟩
  by_cases hs : 0 ≤ (D.phase-C.phase).sin
  · rw [abs_of_nonneg hs] at hs0 hs1
    refine ⟨pointInDirection o C.phase (1/5) (2/5),?_,?_⟩
    · apply (C.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha.1,ha.2]
    · rw [pointInDirection_transition o C.phase D.phase]
      apply (D.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha'.1,ha'.2]
  · rw [abs_of_neg (lt_of_not_ge hs)] at hs0 hs1
    refine ⟨pointInDirection o C.phase (1/5) (-(2/5)),?_,?_⟩
    · apply (C.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha.1,ha.2]
    · rw [pointInDirection_transition o C.phase D.phase]
      apply (D.cartesian _ _).mpr
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith [ha'.1,ha'.2]

/-! ## The containing case -/

/-- The containing alternative of the *strict contact-polygon* theorem. -/
theorem three_containing_impossible (S T U : UnitSquare) (o : Point)
    (hST : Disjoint {z | openSquare S z} {z | openSquare T z})
    (hSU : Disjoint {z | openSquare S z} {z | openSquare U z})
    (hTU : Disjoint {z | openSquare T z} {z | openSquare U z})
    (hS : P3Strict (alpha S o) (beta S o))
    (hT : P3Strict (alpha T o) (beta T o))
    (hU : P3Strict (alpha U o) (beta U o))
    (ho : openSquare S o) : False := by
  obtain ⟨C,hCsort⟩ := sorted_square_chart S o
  obtain ⟨D,hDsort⟩ := sorted_square_chart T o
  obtain ⟨E,hEsort⟩ := sorted_square_chart U o
  have hpC := C.p3Strict hS
  have hpD := D.p3Strict hT
  have hpE := E.p3Strict hU
  have hTo : ¬ openSquare T o := fun h => Set.disjoint_left.mp hST ho h
  have hUo : ¬ openSquare U o := fun h => Set.disjoint_left.mp hSU ho h
  have hDa := D.exterior hDsort hTo
  have hEa := E.exterior hEsort hUo
  have hinside := C.origin.mp ho
  obtain ⟨A,hA⟩ := three_containing_arc_formula C ho
  obtain ⟨B,hB⟩ := three_cap_arc_formula D hDa hpD
  obtain ⟨G,hG⟩ := three_cap_arc_formula E hEa hpE
  have hDdata := three_cap_data hDa D.nonneg.2 hpD
  have hEdata := three_cap_data hEa E.nonneg.2 hpE
  have hDlen : 2*Real.pi/3 < threeCapLength D.a D.b := hDdata.2.2.2.2.2
  have hElen : 2*Real.pi/3 < threeCapLength E.a E.b := hEdata.2.2.2.2.2
  have hbudget := triple_arc_budget A B G hST hSU hTU
  have hLsmall : threeContainingLength C.a C.b < 2*Real.pi/3 := by
    linarith

  let P : ℝ := (1/2-C.a)/auxThree
  let Q : ℝ := (1/2-C.b)/auxThree
  let L : ℝ := threeContainingLength C.a C.b
  let δ : ℝ := 2*Real.pi/3-L
  have hL : L=Real.pi/2+Real.arcsin P+Real.arcsin Q := rfl
  have hδ : δ=2*Real.pi/3-L := rfl
  have hA' : 2*A.halfWidth=L := hA
  obtain ⟨hP0,hPQ,hQ1,hcentral,hδpos0,hδsmall0⟩ :=
    three_deficit_bounds C.nonneg.1 C.nonneg.2 hCsort hinside.1 hinside.2 hpC hLsmall
  change 0 < P at hP0
  change P ≤ Q at hPQ
  change Q < 1 at hQ1
  change 1/2 < (16/13)*P+Q at hcentral
  change Real.pi/6-Real.arcsin P-Real.arcsin Q < 1/12 at hδsmall0
  have hδsmall : δ < 1/12 := by linarith
  have hQ : Q ∈ Icc (0:ℝ) 1 := ⟨hP0.le.trans hPQ,hQ1.le⟩

  have hgapD := three_gap_from_containing C D hCsort ho hDa hpD hST
  have hgapE := three_gap_from_containing C E hCsort ho hEa hpE hSU
  have hgapD' : P ≤ (D.a-1/2)/auxThree :=
    (div_le_div_iff_of_pos_right (by norm_num [auxThree])).mpr hgapD
  have hgapE' : P ≤ (E.a-1/2)/auxThree :=
    (div_le_div_iff_of_pos_right (by norm_num [auxThree])).mpr hgapE
  have hbudD : threeCapLength D.a D.b+L < 4*Real.pi/3 := by linarith
  have hbudE : threeCapLength E.a E.b+L < 4*Real.pi/3 := by linarith
  obtain ⟨hDfull,hDb,hDamax⟩ := three_cap_reduction hDa D.nonneg.2 hpD
    hP0.le hQ hcentral hgapD' hL hδ hδsmall hbudD
  obtain ⟨hEfull,hEb,hEamax⟩ := three_cap_reduction hEa E.nonneg.2 hpE
    hP0.le hQ hcentral hgapE' hL hδ hδsmall hbudE

  let Bfull := threeFullCap D hDa hpD hDfull
  let Gfull := threeFullCap E hEa hpE hEfull
  have hdist := A.third_distance_bounds Bfull Gfull hST hSU hTU
  change
    threeCapA D.a+threeCapA E.a ≤ dist D.phase E.phase ∧
    dist D.phase E.phase ≤ 2*Real.pi-2*A.halfWidth-threeCapA D.a-threeCapA E.a
    at hdist
  have hlo : 2*Real.pi/3 ≤ dist D.phase E.phase := by
    linarith [hDdata.2.2.2.1,hEdata.2.2.2.1,hdist.1]
  have hhi : dist D.phase E.phase < 2*Real.pi/3+1/12 := by
    linarith [hDdata.2.2.2.1,hEdata.2.2.2.1,hdist.2]
  obtain ⟨z,hzT,hzU⟩ := near_axis_square_overlap D E
    ⟨hDa,hDamax⟩ hDb ⟨hEa,hEamax⟩ hEb hlo hhi
  exact Set.disjoint_left.mp hTU hzT hzU

end SquaresInCircles
