import SquaresInCircles.Seven.SectorBounds
import SquaresInCircles.Seven.TaylorBounds

/-!
# Turn bounds for the inward axis

Inequalities on whole intervals of the relative turn, with explicit linear
margins, from Taylor bounds.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Positive turn: the radial extent of the target is the only upper bound used. -/
lemma inward_positive_turn_bound {A v e : ℝ}
    (hA : A ≤ Real.sqrt 3-1/2) (hv : 0 ≤ v)
    (he : 0 ≤ e ∧ e ≤ Real.pi/12) :
    e/840 ≤ (4/5)*e-A*Real.sin e+|Real.sin e|/2+
      (v-1/2)*(1-Real.cos e) := by
  have hs0 : 0 ≤ Real.sin e := Real.sin_nonneg_of_nonneg_of_le_pi
    he.1 (by linarith [he.2,Real.pi_pos])
  have hc0 : 0 ≤ 1-Real.cos e := sub_nonneg.mpr (Real.cos_le_one e)
  have hs := Real.sin_le he.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := e)
  have hroot : Real.sqrt 3 ≤ 26/15 := by linarith [sqrt_three_bounds.2]
  have hroot0 : 0 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have he1 : e ≤ 11/42 := by linarith [he.2,pi_lt_22_over_7]
  have hAprod := mul_nonneg (sub_nonneg.mpr hA) hs0
  have hvprod := mul_nonneg hv hc0
  have hsinprod := mul_nonneg hroot0 (sub_nonneg.mpr hs)
  have hrootprod := mul_nonneg he.1 (show 0 ≤ 26/15-Real.sqrt 3 by linarith)
  have heprod := mul_nonneg he.1 (show 0 ≤ 11/42-e by linarith)
  rw [abs_of_nonneg hs0]
  linarith

/-- A positive whole-interval bound for the negative-turn trigonometric profile. -/
lemma inward_negative_profile {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    (59/3670)*z ≤ Real.sin z-(4/5)*z*Real.cos z-(3/4)*(1-Real.cos z) := by
  have hz9 : z ≤ 9/8 := by linarith [hz.2,pi_lt_22_over_7]
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hcu := cos_upper_four hz.1
  have hm := mul_le_mul_of_nonneg_left hcu hz.1
  have hz2 : z^2 ≤ 81/64 := by nlinarith [hz.1]
  have h5 := mul_nonneg (pow_nonneg hz.1 3)
    (show 0 ≤ 81/64-z^2 by linarith)
  have hpoly : (59/3670 : ℝ) ≤ 1/5-(3/8)*z+(367/1920)*z^2 := by
    have hid : 1/5-(3/8)*z+(367/1920)*z^2-59/3670 =
        (367/1920)*(z-360/367)^2 := by ring
    linarith [sq_nonneg (z-360/367)]
  have hpoly' := mul_le_mul_of_nonneg_left hpoly hz.1
  linarith

/-- Negative turn, given the transverse lower bound that the axial label
implies. -/
lemma inward_negative_turn_bound {A v z : ℝ}
    (hA : 1/2 ≤ A) (hv : (4/5)*z-3/4 ≤ v-1/2)
    (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    (59/3670)*z ≤ (4/5)*(-z)-A*Real.sin (-z)+|Real.sin (-z)|/2+
      (v-1/2)*(1-Real.cos (-z)) := by
  have hs0 : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi
    hz.1 (by linarith [hz.2,Real.pi_pos])
  have hc0 : 0 ≤ 1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hAprod := mul_nonneg (show 0 ≤ A-1/2 by linarith) hs0
  have hvprod := mul_nonneg (sub_nonneg.mpr hv) hc0
  have hp := inward_negative_profile hz
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs0]
  linarith

end SquaresInCircles.Seven
