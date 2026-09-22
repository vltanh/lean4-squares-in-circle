import ThreeUnitSquaresInCircle.Unified.ThreeCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The containing-square deficit and compensation estimates

The variables P,Q,u,v in the compensation lemma are normalized by r=3/8.
The only calculus step is a one-dimensional monotonicity comparison, with
explicit positive square-root denominators. All constants are exact.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

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
    have hg : HasDerivAt (fun z : ℝ => 1/2+(16/13)*z) (16/13) t := by
      simpa only [id_eq,zero_add,mul_one] using
        (hasDerivAt_const t (1/2 : ℝ)).add ((hasDerivAt_id t).const_mul (16/13))
    have hd := ((Real.hasDerivAt_arcsin (by linarith : 1/2+(16/13)*t ≠ -1)
      (by linarith : 1/2+(16/13)*t ≠ 1)).comp t hg).sub
        (Real.hasDerivAt_arcsin (by linarith : t ≠ -1) (by linarith : t ≠ 1))
    simpa only [f,df] using hd
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
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a)
    (ha1 : a < 1/2) (hb1 : b < 1/2) (hp : P3Strict a b)
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

end ThreeUnitSquaresInCircle.Unified
