import ThreeUnitSquaresInCircle.RatDefinitions
import ThreeUnitSquaresInCircle.Geometry

/-!
Real interpretation of the endpoint interval data.

This file uses exact special-angle identities, so neither a numerical value of
pi nor an external series evaluation is assumed. The only angles required are
0, pi/12, pi/8, pi/6, pi/4 and pi/3.
-/
noncomputable section
open scoped BigOperators
namespace ThreeUnitSquaresInCircle.Cert
open RatData

/-- Elementary enclosure of a nonnegative square root by squaring the endpoints. -/
lemma sqrt_enclosure {x l u : ℝ} (hx : 0 ≤ x) (_hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlx : l ^ 2 ≤ x) (hxu : x ≤ u ^ 2) :
    l ≤ Real.sqrt x ∧ Real.sqrt x ≤ u := by
  have hs := Real.sq_sqrt hx
  have hp := Real.sqrt_nonneg x
  constructor <;> nlinarith

lemma sqrt_two_bounds :
    (1414213562373 / 1000000000000 : ℝ) ≤ Real.sqrt 2 ∧
    Real.sqrt 2 ≤ 1414213562374 / 1000000000000 := by
  apply sqrt_enclosure <;> norm_num

lemma sqrt_three_bounds :
    (1732050807568 / 1000000000000 : ℝ) ≤ Real.sqrt 3 ∧
    Real.sqrt 3 ≤ 1732050807569 / 1000000000000 := by
  apply sqrt_enclosure <;> norm_num

lemma sqrt_six_bounds :
    (2449489742783 / 1000000000000 : ℝ) ≤ Real.sqrt 6 ∧
    Real.sqrt 6 ≤ 2449489742784 / 1000000000000 := by
  apply sqrt_enclosure <;> norm_num

lemma sqrt_two_mul_sqrt_three : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma cos_pi_div_twelve :
    Real.cos (Real.pi / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
  rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring,
    Real.cos_sub, Real.cos_pi_div_four, Real.cos_pi_div_six,
    Real.sin_pi_div_four, Real.sin_pi_div_six]
  nlinarith [sqrt_two_mul_sqrt_three]

lemma sin_pi_div_twelve :
    Real.sin (Real.pi / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
  rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring,
    Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_six,
    Real.cos_pi_div_four, Real.sin_pi_div_six]
  nlinarith [sqrt_two_mul_sqrt_three]

def angleReal : Angle → ℝ
  | .zero => 0
  | .a15 => Real.pi / 12
  | .a22_5 => Real.pi / 8
  | .a30 => Real.pi / 6
  | .a45 => Real.pi / 4
  | .a60 => Real.pi / 3

/-- The stored rational cosine intervals are genuine enclosures in the reals. -/
theorem cosInterval_sound (a : Angle) :
    ((cosInterval a).1 : ℝ) ≤ Real.cos (angleReal a) ∧
    Real.cos (angleReal a) ≤ ((cosInterval a).2 : ℝ) := by
  have h2 := sqrt_two_bounds
  have h3 := sqrt_three_bounds
  have h6 := sqrt_six_bounds
  cases a with
  | zero => norm_num [cosInterval, angleReal]
  | a15 =>
      simp only [angleReal, cos_pi_div_twelve]
      norm_num [cosInterval] at *
      constructor <;> linarith
  | a22_5 =>
      have hr :
          (1847758 / 1000000 : ℝ) ≤ Real.sqrt (2 + Real.sqrt 2) ∧
          Real.sqrt (2 + Real.sqrt 2) ≤ 1847760 / 1000000 := by
        apply sqrt_enclosure
        · positivity
        · norm_num
        · norm_num
        · nlinarith
        · nlinarith
      simp only [angleReal, Real.cos_pi_div_eight]
      norm_num [cosInterval]
      constructor <;> linarith
  | a30 =>
      simp only [angleReal, Real.cos_pi_div_six]
      norm_num [cosInterval]
      constructor <;> linarith
  | a45 =>
      simp only [angleReal, Real.cos_pi_div_four]
      norm_num [cosInterval]
      constructor <;> linarith
  | a60 => norm_num [cosInterval, angleReal, Real.cos_pi_div_three]

/-- The stored rational sine intervals are genuine enclosures in the reals. -/
theorem sinInterval_sound (a : Angle) :
    ((sinInterval a).1 : ℝ) ≤ Real.sin (angleReal a) ∧
    Real.sin (angleReal a) ≤ ((sinInterval a).2 : ℝ) := by
  have h2 := sqrt_two_bounds
  have h3 := sqrt_three_bounds
  have h6 := sqrt_six_bounds
  cases a with
  | zero => norm_num [sinInterval, angleReal]
  | a15 =>
      simp only [angleReal, sin_pi_div_twelve]
      norm_num [sinInterval] at *
      constructor <;> linarith
  | a22_5 =>
      have hr :
          (765366 / 1000000 : ℝ) ≤ Real.sqrt (2 - Real.sqrt 2) ∧
          Real.sqrt (2 - Real.sqrt 2) ≤ 765368 / 1000000 := by
        apply sqrt_enclosure
        · nlinarith
        · norm_num
        · norm_num
        · nlinarith
        · nlinarith
      simp only [angleReal, Real.sin_pi_div_eight]
      norm_num [sinInterval]
      constructor <;> linarith
  | a30 => norm_num [sinInterval, angleReal, Real.sin_pi_div_six]
  | a45 =>
      simp only [angleReal, Real.sin_pi_div_four]
      norm_num [sinInterval]
      constructor <;> linarith
  | a60 =>
      simp only [angleReal, Real.sin_pi_div_three]
      norm_num [sinInterval]
      constructor <;> linarith

/-- Sign-sensitive interval multiplication; this is the real soundness of termLower. -/
lemma termLower_sound (q : ℚ) (I : ℚ × ℚ) (x : ℝ)
    (hx : (I.1 : ℝ) ≤ x ∧ x ≤ (I.2 : ℝ)) :
    (termLower q I : ℝ) ≤ (q : ℝ) * x := by
  unfold termLower
  split_ifs with hq
  · push_cast
    exact mul_le_mul_of_nonneg_left hx.1 (by exact_mod_cast hq)
  · push_cast
    exact mul_le_mul_of_nonpos_left hx.2 (by exact_mod_cast (le_of_lt (lt_of_not_ge hq)))

end ThreeUnitSquaresInCircle.Cert
