import SquaresInCircles.Three.Exterior
import SquaresInCircles.Common.Coordinates
import SquaresInCircles.Common.ArcMetric
import SquaresInCircles.Common.ElementaryTrig
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The containing square, three squares

If the disk centre lies inside one square, the other two are exterior. Three
disjoint arc witnesses on the circle of radius `3/8` bound the containing
square's deficit. A clipped exterior cap would compensate for that entire
deficit. Otherwise both exterior caps are full and nearly axial, the circle
perimeter inequality pins the angle between them, and an explicit point lies in
both, contradicting interior-disjointness. Only the containing square needs the
strict 16-gon, so the same argument serves the optimum and its uniqueness.
-/
noncomputable section
open Set
namespace SquaresInCircles

/-! ## Deficit and compensation estimates

The variables `P`, `Q`, `u`, `v` of the compensation lemma are normalized by
the auxiliary radius `3/8`. The only calculus step is a one-dimensional
monotonicity comparison, with explicit positive square-root denominators. -/

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
    (hcentral : 1/2 < (16/13)*P+Q) (hPu : P ≤ u)
    (hv : 1/2+(16/13)*u ≤ v) (hv1 : v < 1) :
    4*Real.pi/3 <
      (Real.pi/2-Real.arcsin u+Real.arcsin v)+
      (Real.pi/2+Real.arcsin P+Real.arcsin Q) := by
  have htop : 1/2+(16/13)*u < 1 := hv.trans_lt hv1
  have hinc := three_asin_increment_mono hP hPu (by linarith) htop
  have hvmono := Real.arcsin_le_arcsin hv
  have htP : 1/2+(16/13)*P ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  have hpair := arcsin_sum_gt_of_sin_lt htP hQ
    (show Real.pi/6 ∈ Icc (0:ℝ) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
    (by rw [Real.sin_pi_div_six]; linarith)
  linarith

/-- The deficit bounds use the two first contact tangents, not numerical trig. -/
lemma three_deficit_bounds {a b : ℝ} (hba : b ≤ a) (ha1 : a < 1/2) (hp : P3Strict a b)
    (hlen : Real.pi/2+Real.arcsin ((1/2-a)/auxThree)+
      Real.arcsin ((1/2-b)/auxThree) ≤ 2*Real.pi/3) :
    0 < (1/2-a)/auxThree ∧ (1/2-a)/auxThree ≤ (1/2-b)/auxThree ∧
      (1/2-b)/auxThree < 1 ∧ 1/2 < (16/13)*((1/2-a)/auxThree)+(1/2-b)/auxThree ∧
      Real.pi/6-Real.arcsin ((1/2-a)/auxThree)-Real.arcsin ((1/2-b)/auxThree) < 1/12 := by
  have hP : 0 < (1/2-a)/auxThree := by dsimp [auxThree]; linarith
  have hPQ : (1/2-a)/auxThree ≤ (1/2-b)/auxThree := by dsimp [auxThree]; linarith
  have hcentral : 1/2 < (16/13)*((1/2-a)/auxThree)+(1/2-b)/auxThree := by
    dsimp [auxThree]; linarith [hp.1]
  have hQ1 : (1/2-b)/auxThree < 1 := by
    apply Real.arcsin_lt_pi_div_two.mp
    linarith [Real.pi_pos,Real.arcsin_pos.mpr hP]
  have hAP := arcsin_ge_self hP.le (hPQ.trans hQ1.le)
  have hAQ := arcsin_ge_self (hP.le.trans hPQ) hQ1.le
  exact ⟨hP,hPQ,hQ1,hcentral,by linarith [pi_lt_22_over_7]⟩

/-- A cap within 1/24 radians of pi/3 has radial coordinate > 9/20. -/
lemma three_cap_near_axis {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2)
    (hA : Real.arccos u < Real.pi/3+1/24) : 9/20 < u := by
  have hAlow : Real.pi/3 ≤ Real.arccos u := by
    have h := arcsin_le_sixth hu0 hu1
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
  linarith

/-! ## Arc witnesses

The containing witness is only an interval known to lie in the square; it is
never assumed to be the entire intersection. The exterior witness has a
specified clipped-cap length; once clipping is excluded, it is centred on the
square's radial phase. -/

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
      2*A.halfWidth=Real.pi/2+Real.arcsin ((1/2-C.a)/auxThree)+
        Real.arcsin ((1/2-C.b)/auxThree) := by
  have hc := C.origin.mp ho
  have hP0 := Real.arcsin_pos.mpr
    (show 0 < (1/2-C.a)/auxThree by dsimp [auxThree]; linarith [hc.1])
  have hQ0 := Real.arcsin_pos.mpr
    (show 0 < (1/2-C.b)/auxThree by dsimp [auxThree]; linarith [hc.2])
  obtain ⟨A,hA,-⟩ := C.arc auxThree
    (-Real.arcsin ((1/2-C.b)/auxThree))
    (Real.pi/2+Real.arcsin ((1/2-C.a)/auxThree))
    (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos,Real.arcsin_le_pi_div_two ((1/2-C.a)/auxThree),
      Real.arcsin_le_pi_div_two ((1/2-C.b)/auxThree)])
    (fun t ht => three_containing_mem C.nonneg.1 C.nonneg.2 hc.1 hc.2 ht)
  exact ⟨A,by rw [hA]; ring⟩

/-- Disjointness from the inscribed disk forces the exterior radial gap. -/
lemma three_gap_from_containing {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hCsort : C.b ≤ C.a) (ho : openSquare S o)
    (hDa : 1/2 ≤ D.a) (hDp : P3 D.a D.b)
    (hd : Disjoint {z | openSquare S z} {z | openSquare T z}) :
    1/2-C.a ≤ D.a-1/2 := by
  by_contra hn
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
  have hαβ : alpha S o ≤ C.a ∧ beta S o ≤ C.a := by
    rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> constructor <;> linarith
  have hzS : openSquare S z := by
    apply inscribed_disk_mem S o (a := C.a) (p := 1/2-C.a)
      (by linarith [hc.1]) (by ring) hαβ.1 hαβ.2
    rw [show z=pointInDirection o D.phase t 0 by rfl,pointInDirection_norm]
    nlinarith
  exact Set.disjoint_left.mp hd hzS hzT

/-- The budget excludes clipping, and forces a small transverse center coordinate. -/
lemma three_cap_reduction {a b P Q : ℝ}
    (ha : 1/2 ≤ a) (hb : 0 ≤ b) (hp : P3 a b)
    (hP : 0 ≤ P) (hQ : Q ∈ Icc (0:ℝ) 1)
    (hcentral : 1/2 < (16/13)*P+Q) (hgap : P ≤ (a-1/2)/auxThree)
    (hδ : Real.pi/6-Real.arcsin P-Real.arcsin Q < 1/12)
    (hbudget : threeCapLength a b+(Real.pi/2+Real.arcsin P+Real.arcsin Q) ≤ 4*Real.pi/3) :
    threeCapA a ≤ threeCapV b ∧ b < 1/16 ∧ a ≤ 11/16 := by
  obtain ⟨hx0,hx1,hv,hA,hAp,hmin⟩ := three_cap_data ha hb hp
  have hfull : threeCapA a ≤ threeCapV b := by
    by_contra hn
    have hclip : threeCapV b < threeCapA a := lt_of_not_ge hn
    have hv1 : (1/2-b)/auxThree < 1 :=
      Real.arcsin_lt_pi_div_two.mp (hclip.trans_le hAp)
    have hcomp := three_compensation hP hQ hcentral hgap hv hv1
    rw [threeCapLength,min_eq_right (by linarith)] at hbudget
    dsimp [threeCapA,threeCapV,Real.arccos] at hbudget
    linarith
  have hlen : threeCapLength a b=2*threeCapA a := min_eq_left (by linarith)
  have hnear : threeCapA a < Real.pi/3+1/24 := by rw [hlen] at hbudget; linarith
  have hrad := three_cap_near_axis hx0 hx1 hnear
  dsimp [auxThree] at hrad
  exact ⟨hfull,by linarith [hp.2.2.1],by linarith [hp.2.2.1]⟩

/-! ## Two nearly axial squares overlap

If two squares have small transverse chart coordinates and their radial phases
differ by between `2*pi/3` and `2*pi/3+1/12`, an explicit point lies in the
open interiors of both. -/

lemma near_axis_angles {φ ψ : Direction}
    (hlo : 2*Real.pi/3 ≤ dist φ ψ)
    (hhi : dist φ ψ < 2*Real.pi/3+1/12) :
    -(3/5:ℝ) < (ψ-φ).cos ∧ (ψ-φ).cos ≤ -1/2 ∧
      4/5 < |(ψ-φ).sin| ∧ |(ψ-φ).sin| < 7/8 := by
  have hcle : (ψ-φ).cos ≤ -1/2 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (direction_diameter φ ψ) hlo
    rw [cos_two_pi_thirds,← cos_sub_distance] at h
    linarith
  let ε := dist φ ψ-2*Real.pi/3
  have hε0 : 0 ≤ ε := by dsimp [ε]; linarith
  have hε1 : ε < 1/12 := by dsimp [ε]; linarith
  have hεpi : ε ≤ Real.pi := by dsimp [ε]; linarith [Real.pi_pos,direction_diameter φ ψ]
  have hsε0 := Real.sin_nonneg_of_nonneg_of_le_pi hε0 hεpi
  have hsε1 := Real.sin_le hε0
  have hprod := mul_nonneg hsε0 (sub_nonneg.mpr (Real.sin_le_one (2*Real.pi/3)))
  have hid : (ψ-φ).cos =
      -(1/2)*Real.cos ε-Real.sin (2*Real.pi/3)*Real.sin ε := by
    rw [cos_sub_distance,show dist φ ψ=2*Real.pi/3+ε by dsimp [ε]; ring,Real.cos_add,
      cos_two_pi_thirds]
  have hclo : -(3/5:ℝ) < (ψ-φ).cos := by linarith [Real.cos_le_one ε]
  have hu := Real.Angle.cos_sq_add_sin_sq (ψ-φ)
  have hsabs := abs_nonneg (ψ-φ).sin
  have hssq : |(ψ-φ).sin|^2=(ψ-φ).sin^2 := sq_abs _
  have hcSqUp : (ψ-φ).cos^2 < (3/5:ℝ)^2 := by
    have h := mul_pos (show 0 < (ψ-φ).cos+3/5 by linarith)
      (show 0 < 3/5-(ψ-φ).cos by linarith)
    linarith
  have hcSqLo : (1/2:ℝ)^2 ≤ (ψ-φ).cos^2 := by
    have h := mul_nonneg (show 0 ≤ -(ψ-φ).cos-1/2 by linarith)
      (show 0 ≤ -(ψ-φ).cos+1/2 by linarith)
    linarith
  refine ⟨hclo,hcle,?_,?_⟩
  · by_contra hn
    have h := mul_nonneg (show 0 ≤ 4/5-|(ψ-φ).sin| by linarith)
      (show 0 ≤ 4/5+|(ψ-φ).sin| by positivity)
    linarith
  · by_contra hn
    have h := mul_nonneg (show 0 ≤ |(ψ-φ).sin|-7/8 by linarith)
      (show 0 ≤ |(ψ-φ).sin|+7/8 by positivity)
    linarith

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

/-- The containing alternative: the square that contains `o` needs the strict
16-gon, the other two only the closed one. -/
theorem three_containing_impossible (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (i : Fin 3) (ho : openSquare (S i) o)
    (hS : P3Strict (alpha (S i) o) (beta (S i) o))
    (hp : ∀ j, P3 (alpha (S j) o) (beta (S j) o)) : False := by
  obtain ⟨j,k,hij,hik,hjk⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases i <;> decide
  have hST := hd.pairwise hij
  have hSU := hd.pairwise hik
  have hTU := hd.pairwise hjk
  obtain ⟨C,hCsort⟩ := sorted_square_chart (S i) o
  obtain ⟨D,hDsort⟩ := sorted_square_chart (S j) o
  obtain ⟨E,hEsort⟩ := sorted_square_chart (S k) o
  have hpC := C.transfer P3Strict p3Strict_swap hS
  have hpD := D.transfer P3 p3_swap (hp j)
  have hpE := E.transfer P3 p3_swap (hp k)
  have hDa := D.exterior hDsort fun h => Set.disjoint_left.mp hST ho h
  have hEa := E.exterior hEsort fun h => Set.disjoint_left.mp hSU ho h
  have hinside := C.origin.mp ho
  obtain ⟨A,hA⟩ := three_containing_arc_formula C ho
  obtain ⟨B,hB,hBc⟩ := three_cap_arc_formula D hDa hpD
  obtain ⟨G,hG,hGc⟩ := three_cap_arc_formula E hEa hpE
  have hDdata := three_cap_data hDa D.nonneg.2 hpD
  have hEdata := three_cap_data hEa E.nonneg.2 hpE
  have hbudget := triple_arc_budget A B G hST hSU hTU
  obtain ⟨hP0,hPQ,hQ1,hcentral,hδ⟩ := three_deficit_bounds hCsort hinside.1 hpC
    (by linarith [hDdata.2.2.2.2.2,hEdata.2.2.2.2.2])
  have hQ : (1/2-C.b)/auxThree ∈ Icc (0:ℝ) 1 := ⟨hP0.le.trans hPQ,hQ1.le⟩
  have hgapD := three_gap_from_containing C D hCsort ho hDa hpD hST
  have hgapE := three_gap_from_containing C E hCsort ho hEa hpE hSU
  obtain ⟨hDfull,hDb,hDamax⟩ := three_cap_reduction hDa D.nonneg.2 hpD hP0.le hQ
    hcentral (by dsimp [auxThree]; linarith) hδ (by linarith [hEdata.2.2.2.2.2])
  obtain ⟨hEfull,hEb,hEamax⟩ := three_cap_reduction hEa E.nonneg.2 hpE hP0.le hQ
    hcentral (by dsimp [auxThree]; linarith) hδ (by linarith [hDdata.2.2.2.2.2])
  have hdist := A.third_distance_bounds B G hST hSU hTU
  rw [hBc hDfull,hGc hEfull] at hdist
  have hBw : threeCapLength D.a D.b=2*threeCapA D.a := min_eq_left (by linarith)
  have hGw : threeCapLength E.a E.b=2*threeCapA E.a := min_eq_left (by linarith)
  obtain ⟨z,hzT,hzU⟩ := near_axis_square_overlap D E ⟨hDa,hDamax⟩ hDb ⟨hEa,hEamax⟩ hEb
    (by linarith [hDdata.2.2.2.1,hEdata.2.2.2.1])
    (by linarith [hDdata.2.2.2.1,hEdata.2.2.2.1])
  exact Set.disjoint_left.mp hTU hzT hzU

end SquaresInCircles
