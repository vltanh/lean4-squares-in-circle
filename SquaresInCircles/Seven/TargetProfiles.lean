import SquaresInCircles.Seven.ScalarPolynomials
import SquaresInCircles.Seven.SectorBounds
import SquaresInCircles.Seven.TaylorBounds

/-!
# Target profiles

The support of a negative target along the boundary of the label regions,
bounded below through the polynomial certificates.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma large_axial_target_profile {z : ℝ}
    (hz : 1/3 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-
      Real.sqrt (13/2)*(Real.cos (z/2)-Real.sin (z/2)) := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hzu : z ≤ 11/7 := by linarith [hz.2,pi_lt_22_over_7]
  have hp := largeAxialP_pos ⟨hz.1,hzu⟩
  have hc := cos_lower_six hz0
  have hch := cos_upper_four (show 0 ≤ z/2 by linarith)
  have hsh := sin_lower_seven (show 0 ≤ z/2 by linarith)
  have hdiff : 0 ≤ Real.cos (z/2)-Real.sin (z/2) :=
    sub_nonneg.mpr (sin_le_cos_of_small ⟨by linarith,by linarith [hz.2]⟩)
  have hroot : Real.sqrt (13/2) < (51:ℝ)/20 := by
    have hh := Real.sq_sqrt (show (0:ℝ) ≤ 13/2 by norm_num)
    nlinarith [Real.sqrt_nonneg (13/2:ℝ)]
  have hmul := mul_nonneg (show 0 ≤ (51:ℝ)/20-Real.sqrt (13/2) by linarith) hdiff
  dsimp [largeAxialP,cos6,cos4,sin7] at hp
  linarith [pi_lower_157]

def smallTargetNu (z : ℝ) : ℝ := (3/40)*(1-2*Real.sin z)
def smallTargetL (z : ℝ) : ℝ :=
  Real.cos z-11/40-Real.pi/60-(4/5)*z+(51/20+3*Real.pi/10)*Real.sin z
def smallTargetRad (z : ℝ) : ℝ :=
  (Real.cos z-9*smallTargetNu z)^2+(1-Real.sin z-11*smallTargetNu z)^2

lemma smallTargetNu_nonneg {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/3) :
    0 ≤ smallTargetNu z := by
  have hh := Real.sin_le hz.1
  dsimp [smallTargetNu]
  linarith [hz.2]

lemma smallTargetRad_expand (z : ℝ) :
    smallTargetRad z = 1189/800-(27/20)*Real.cos z+
      (27/10)*Real.cos z*Real.sin z+(249/200)*Real.sin z^2-
      (319/200)*Real.sin z := by
  dsimp [smallTargetRad,smallTargetNu]
  linarith [Real.sin_sq_add_cos_sq z]

lemma smallAxialL_gt_half {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/3) :
    (1:ℝ)/2 < smallAxialL z := by
  have hz2 : z^2 ≤ (1/3:ℝ)^2 := by nlinarith
  have hz3 : z^3 ≤ (1/3:ℝ)^3 := pow_le_pow_left₀ hz.1 hz.2 3
  have hp4 := mul_nonneg (pow_nonneg hz.1 4)
    (show 0 ≤ 1/24-z^2/720 by linarith)
  have hp5 := mul_nonneg (pow_nonneg hz.1 5)
    (show 0 ≤ 1/120-z^2/5040 by linarith)
  have hlin := mul_nonneg hz.1 (show (0:ℝ) ≤ 873/250-4/5 by norm_num)
  dsimp [smallAxialL,cos6,sin7]
  linarith

lemma smallTargetL_lower {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/3) :
    smallAxialL z ≤ smallTargetL z := by
  have hc := cos_lower_six hz.1
  have hs := sin_lower_seven hz.1
  have hs0 : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,pi_lower_157])
  have hcoeff := mul_nonneg
    (show 0 ≤ 51/20+3*Real.pi/10-873/250 by linarith [pi_lower_157]) hs0
  dsimp [smallAxialL,smallTargetL,cos6,sin7]
  linarith [pi_lt_22_over_7]

lemma smallTargetRad_upper {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/3) :
    smallTargetRad z ≤ smallAxialU z := by
  have hcL := cos_lower_six hz.1
  have hcU := cos_upper_four hz.1
  have hsL := sin_lower_seven hz.1
  have hsU := sin_upper_five hz.1
  have hs0 : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,pi_lower_157])
  have hc0 : 0 ≤ Real.cos z := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [hz.1,Real.pi_pos],by linarith [hz.2,pi_lower_157]⟩
  have hcs := mul_le_mul hcU hsU hs0 (hc0.trans hcU)
  have hcos2 := cos_sq_lower_six hz.1
  have hsin2 : Real.sin z^2 ≤ z^2-z^4/3+2*z^6/45 := by
    linarith [Real.sin_sq_add_cos_sq z]
  rw [smallTargetRad_expand]
  dsimp [smallAxialU,cos6,cos4,sin5,sin7]
  linarith

lemma small_axial_target_profile {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/3) :
    0 < smallTargetL z-radius*Real.sqrt (smallTargetRad z) := by
  have hp := smallAxial_discriminant_pos hz
  have hL := smallTargetL_lower hz
  have hL0 := smallAxialL_gt_half hz
  have hU := smallTargetRad_upper hz
  have hr0 : 0 ≤ smallTargetRad z := by unfold smallTargetRad; positivity
  have hN2 : (radius*Real.sqrt (smallTargetRad z))^2 = (13/4)*smallTargetRad z := by
    rw [mul_pow,radius_sq,Real.sq_sqrt hr0]
  have hNN := lt_of_pow_lt_pow_left₀ 2 (by linarith : (0:ℝ) ≤ smallAxialL z)
    (show (radius*Real.sqrt (smallTargetRad z))^2 < (smallAxialL z)^2 by linarith)
  linarith

/-- The axial inequality is used as a dual constraint, not as a replacement
for disk containment. -/
lemma axial_target_small_support {A v z : ℝ}
    (h : Admissible A v) (hA : label A v=axial v)
    (hz : 0 ≤ z ∧ z ≤ 1/3) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-
      (A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  let n := smallTargetNu z
  have hn : 0 ≤ n := smallTargetNu_nonneg hz
  have ha := axial_tie_line h hA
  have hfar : 9*(A+1/2)+11*(v+1/2) ≤ 2*Real.pi+17 := by linarith
  have hw := mul_le_mul_of_nonneg_left hfar hn
  have hdot := dot_lower_candidate
    (p := -(Real.cos z-9*n)) (r := -(1-Real.sin z-11*n)) h.2.2.2
  have hid : (-(Real.cos z-9*n))^2+(-(1-Real.sin z-11*n))^2 = smallTargetRad z := by
    dsimp [n,smallTargetRad]
    ring
  rw [hid] at hdot
  have hprof := small_axial_target_profile hz
  have hLid : 1+2*Real.pi/15-(4/5)*z+Real.cos z-n*(2*Real.pi+17) =
      smallTargetL z := by
    dsimp [n,smallTargetNu,smallTargetL]
    ring
  linarith

lemma axial_target_large_support {A v z : ℝ}
    (h : Admissible A v) (hz : 1/3 ≤ z ∧ z ≤ Real.pi/2) :
    0 < 1+2*Real.pi/15-(4/5)*z+Real.cos z-
      (A+1/2)*Real.cos z-(v+1/2)*(1-Real.sin z) := by
  have hc0 : 0 ≤ Real.cos (z/2)-Real.sin (z/2) :=
    sub_nonneg.mpr (sin_le_cos_of_small ⟨by linarith [hz.1],by linarith [hz.2]⟩)
  have hdot := dot_lower_candidate (p := -Real.cos z) (r := -(1-Real.sin z)) h.2.2.2
  have hunit : Real.cos z^2+(1-Real.sin z)^2 =
      2*(Real.cos (z/2)-Real.sin (z/2))^2 := by
    have hsin : Real.sin z=2*Real.sin (z/2)*Real.cos (z/2) := by
      rw [← Real.sin_two_mul]; ring_nf
    linarith [Real.sin_sq_add_cos_sq z,Real.sin_sq_add_cos_sq (z/2)]
  have hrad : radius*Real.sqrt ((-Real.cos z)^2+(-(1-Real.sin z))^2) =
      Real.sqrt (13/2)*(Real.cos (z/2)-Real.sin (z/2)) := by
    have hs := Real.sq_sqrt (show 0 ≤ (-Real.cos z)^2+(-(1-Real.sin z))^2 by positivity)
    have ht := Real.sq_sqrt (show (0:ℝ) ≤ 13/2 by norm_num)
    have hleft : 0 ≤ radius*Real.sqrt ((-Real.cos z)^2+(-(1-Real.sin z))^2) :=
      mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
    have hright := mul_nonneg (Real.sqrt_nonneg (13/2:ℝ)) hc0
    have he : (radius*Real.sqrt ((-Real.cos z)^2+(-(1-Real.sin z))^2))^2 =
        (Real.sqrt (13/2)*(Real.cos (z/2)-Real.sin (z/2)))^2 := by
      rw [mul_pow,mul_pow,radius_sq,hs,ht]
      linarith
    exact (sq_eq_sq₀ hleft hright).mp he
  have hprof := large_axial_target_profile hz
  linarith

def shortTargetL (z : ℝ) : ℝ := Real.cos z-2/15-(4/5)*z
def shortTargetRad (z : ℝ) : ℝ :=
  (3/5-Real.cos z)^2+(4/15-Real.sin z)^2

lemma short_target_profile {z : ℝ} (hz : 0 < z ∧ z ≤ 1/6) :
    0 < shortTargetL z-radius*Real.sqrt (shortTargetRad z) := by
  have hp := shortSideH_pos ⟨hz.1.le,hz.2⟩
  have hs := mul_pos hz.1 hp
  have hc2 := cos_sq_lower_six hz.1.le
  have hcL := cos_lower_six hz.1.le
  have hcU := cos_upper_four hz.1.le
  have hsL := sin_lower_seven hz.1.le
  have hzc := mul_le_mul_of_nonneg_left hcU hz.1.le
  have hid : (shortTargetL z)^2-(13/4)*shortTargetRad z =
      Real.cos z^2+(109/30)*Real.cos z-(8/5)*z*Real.cos z+
      (16/25)*z^2+(16/75)*z+(26/15)*Real.sin z-139/30 := by
    dsimp [shortTargetL,shortTargetRad]
    linarith [Real.sin_sq_add_cos_sq z]
  have hpoly : z*shortSideH z ≤ (shortTargetL z)^2-(13/4)*shortTargetRad z := by
    rw [hid]
    dsimp [shortSideH,cos6,cos4,sin7] at *
    linarith [pow_nonneg hz.1.le 4]
  have hL0 : 0 < shortTargetL z := by
    have hc := Real.one_sub_sq_div_two_le_cos (x := z)
    dsimp [shortTargetL]
    linarith [mul_le_mul_of_nonneg_left hz.2 hz.1.le]
  have hrad0 : 0 ≤ shortTargetRad z := by unfold shortTargetRad; positivity
  have hN2 : (radius*Real.sqrt (shortTargetRad z))^2=(13/4)*shortTargetRad z := by
    rw [mul_pow,radius_sq,Real.sq_sqrt hrad0]
  have hN := lt_of_pow_lt_pow_left₀ 2 hL0.le
    (show (radius*Real.sqrt (shortTargetRad z))^2 < (shortTargetL z)^2 by linarith)
  linarith

end SquaresInCircles.Seven
