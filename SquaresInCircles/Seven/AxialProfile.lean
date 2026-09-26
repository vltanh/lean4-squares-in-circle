import SquaresInCircles.Seven.ScalarPolynomials
import SquaresInCircles.Seven.SectorBounds
import SquaresInCircles.Seven.TaylorBounds

/-!
# The axial profile

`sin z - (4/5) z cos z - (7/8)(1 - cos z)` is nonnegative on `[0, π/2]`, by
Taylor bounds and two Bernstein certificates split at `z = 35/32`, where the
coefficient of `cos z` changes sign.
-/
noncomputable section
namespace SquaresInCircles.Seven

def axialProfile (z : ℝ) : ℝ :=
  Real.sin z-(4/5)*z*Real.cos z-(7/8)*(1-Real.cos z)

lemma axial_profile_nonneg {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/2) :
    0 ≤ axialProfile z := by
  have hs := sin_lower_seven hz.1
  by_cases hsmall : z ≤ 35/32
  · have hc : 0 ≤ 7/8-(4/5)*z := by linarith
    have hm := mul_le_mul_of_nonneg_left (cos_lower_six hz.1) hc
    have hp := mul_nonneg hz.1 (axialSmallQ_pos ⟨hz.1,hsmall⟩).le
    have hid := axialSmall_identity z
    dsimp [axialProfile,sin7,cos6] at *
    linarith
  · have hzU : z ≤ 11/7 := by linarith [hz.2,pi_lt_22_over_7]
    have hc : 7/8-(4/5)*z ≤ 0 := by linarith
    have hm := mul_le_mul_of_nonpos_left (cos_upper_four hz.1) hc
    have hp := axialLargeP_pos ⟨le_of_not_ge hsmall,hzU⟩
    dsimp [axialProfile,axialLargeP,sin7,cos4] at *
    linarith

end SquaresInCircles.Seven
