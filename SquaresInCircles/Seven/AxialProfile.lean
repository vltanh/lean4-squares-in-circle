import SquaresInCircles.Seven.ScalarPolynomials
import SquaresInCircles.Seven.SectorBounds
import SquaresInCircles.Seven.TaylorBounds

/-!
# The axial profile

`sin z - (4/5) z cos z - (7/8)(1 - cos z)` is positive on `(0, π/2]`, by
Taylor bounds and two Bernstein certificates split at `z = 35/32`, where the
coefficient of `cos z` changes sign.
-/
noncomputable section
namespace SquaresInCircles.Seven

def axialProfile (z : ℝ) : ℝ :=
  Real.sin z-(4/5)*z*Real.cos z-(7/8)*(1-Real.cos z)

lemma axial_profile_pos {z : ℝ} (hz : 0 < z ∧ z ≤ Real.pi/2) :
    0 < axialProfile z := by
  have hz0 : 0 ≤ z := hz.1.le
  have hs := sin_lower_seven hz0
  by_cases hsmall : z ≤ 35/32
  · have hc : 0 ≤ 7/8-(4/5)*z := by linarith
    have hm := mul_le_mul_of_nonneg_left (cos_lower_six hz0) hc
    have hp := mul_pos hz.1 (axialSmallQ_pos ⟨hz0,hsmall⟩)
    have hid := axialSmall_identity z
    dsimp [axialProfile,sin7,cos6] at *
    linarith
  · have hzU : z ≤ 11/7 := by linarith [hz.2,pi_lt_22_over_7]
    have hc : 7/8-(4/5)*z ≤ 0 := by linarith
    have hm := mul_le_mul_of_nonpos_left (cos_upper_four hz0) hc
    have hp := axialLargeP_pos ⟨le_of_not_ge hsmall,hzU⟩
    dsimp [axialProfile,axialLargeP,sin7,cos4] at *
    linarith

lemma axial_profile_nonneg {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 ≤ axialProfile z := by
  rcases eq_or_lt_of_le hz.1 with hzero | hpos
  · rw [← hzero]
    norm_num [axialProfile]
  · exact (axial_profile_pos ⟨hpos,hz.2⟩).le

/-- A smaller coefficient of `1-cos z` only improves the lower bound. -/
lemma axial_profile_parameter_nonneg {b z : ℝ}
    (hb : b ≤ 7/8) (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 ≤ Real.sin z-(4/5)*z*Real.cos z-b*(1-Real.cos z) := by
  have hh := axial_profile_nonneg hz
  have hm := mul_nonneg (sub_nonneg.mpr hb)
    (sub_nonneg.mpr (Real.cos_le_one z))
  dsimp [axialProfile] at hh
  linarith

end SquaresInCircles.Seven
