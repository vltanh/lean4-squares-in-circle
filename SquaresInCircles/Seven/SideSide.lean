import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.TaylorBounds

/-!
# Global side--side support certificate

This is the complete scalar/Cauchy--Schwarz argument for the opposite-sign,
side-selected pair. It is not restricted to a neighborhood of the contact.
All signs are proved by polynomial inequalities and Taylor bounds.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

private lemma abs_min_identity (x : ℝ) : |x| = x-2*min x 0 := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h, min_eq_right h]; ring
  · rw [abs_of_nonpos (le_of_not_ge h), min_eq_left (le_of_not_ge h)]; ring

def sideSideL (w : ℝ) : ℝ :=
  19/20+Real.cos w-min (Real.sin w) 0-(6/5)*w

def sideSideRadicand (w : ℝ) : ℝ :=
  (Real.sin w-9/10)^2+(2/5-Real.cos w)^2

private lemma cos_ge_half {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    (1/2 : ℝ) ≤ Real.cos z := by
  have h := Real.strictAntiOn_cos.antitoneOn
    (show z ∈ Icc (0 : ℝ) Real.pi by constructor <;> linarith [hz.1,hz.2,Real.pi_pos])
    (show Real.pi/3 ∈ Icc (0 : ℝ) Real.pi by constructor <;> linarith [Real.pi_pos]) hz.2
  simpa only [Real.cos_pi_div_three] using h

lemma sideSideL_pos {w : ℝ} (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    0 < sideSideL w := by
  have hpi := Real.pi_lt_d4
  by_cases h : 0 ≤ w
  · have hs := Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith [hw.2,Real.pi_pos])
    have hc := Real.one_sub_sq_div_two_le_cos (x := w)
    have hw' : w < 8/15 := by linarith [hw.2]
    unfold sideSideL
    rw [min_eq_right hs]
    nlinarith
  · have hz : 0 ≤ -w ∧ -w ≤ Real.pi/3 := ⟨by linarith,by linarith [hw.1]⟩
    have hc := cos_ge_half hz
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_pos])
    have hs' : Real.sin w ≤ 0 := by
      rw [Real.sin_neg] at hs
      linarith
    unfold sideSideL
    rw [min_eq_left hs']
    rw [Real.cos_neg] at hc
    linarith

lemma sideSide_margin_pos {w : ℝ}
    (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) (hne : w ≠ 0) :
    0 < (sideSideL w)^2-targetSq*sideSideRadicand w := by
  have hpi := Real.pi_lt_d4
  by_cases h : 0 < w
  · have hw' : w ≤ 8/15 := by linarith [hw.2]
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi h.le (by linarith [hw.2,Real.pi_pos])
    have hs := Real.sin_ge_sub_cube h.le
    have hc := Real.one_sub_sq_div_two_le_cos (x := w)
    have hcu := cos_upper_four h.le
    have hxc := mul_le_mul_of_nonneg_left hcu h.le
    have hc2 : 1-w^2 ≤ Real.cos w^2 := by
      nlinarith [Real.sin_sq_le_sq (x := w), Real.sin_sq_add_cos_sq w]
    have hpoly :
        w*(468-724*w+90*w^2-40*w^4) ≤
        (19+20*Real.cos w-24*w)^2-
          13*(197-180*Real.sin w-80*Real.cos w) := by
      nlinarith
    have hw4 : w^4 ≤ (8/15 : ℝ)^4 := by gcongr
    have hp : 0 < 468-724*w+90*w^2-40*w^4 := by
      nlinarith [sq_nonneg w]
    have hn := mul_pos h hp
    have hid :
        400*((sideSideL w)^2-targetSq*sideSideRadicand w) =
        (19+20*Real.cos w-24*w)^2-
          13*(197-180*Real.sin w-80*Real.cos w) := by
      unfold sideSideL sideSideRadicand targetSq
      rw [min_eq_right hs0]
      nlinarith [Real.sin_sq_add_cos_sq w]
    linarith
  · let z := -w
    have hz : 0 < z := by dsimp [z]; linarith
    have hzu : z ≤ Real.pi/3 := by dsimp [z]; linarith [hw.1]
    have hz9 : z < 9/8 := by linarith
    have hc := cos_ge_half ⟨hz.le,hzu⟩
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.le (by linarith [hzu,Real.pi_pos])
    have hsU := Real.sin_le hz.le
    have hsL := Real.sin_ge_sub_cube hz.le
    have hcL := Real.one_sub_sq_div_two_le_cos (x := z)
    have hp1 := mul_nonneg (show 0 ≤ Real.cos z-1/2 by linarith) hs0
    have hp2 := mul_nonneg (show 0 ≤ Real.cos z-1/2 by linarith) hz.le
    have hp3 := mul_le_mul_of_nonneg_left hsL hz.le
    let N := 800*Real.cos z*Real.sin z+960*z*Real.cos z+
      1800*(Real.cos z-1)+960*z*Real.sin z-1580*Real.sin z+576*z^2+912*z
    have hN : z*(212+z*(636-160*z^2)) ≤ N := by
      dsimp [N]
      nlinarith
    have hp : 0 < 212+z*(636-160*z^2) := by
      have hi : 0 < 636-160*z^2 := by nlinarith
      have hm := mul_nonneg hz.le hi.le
      linarith
    have hn := mul_pos hz hp
    have hid : 400*((sideSideL w)^2-targetSq*sideSideRadicand w) = N := by
      have he : w = -z := by dsimp [z]; ring
      rw [he]
      unfold sideSideL sideSideRadicand targetSq
      rw [Real.cos_neg,Real.sin_neg,min_eq_left (neg_nonpos.mpr hs0)]
      dsimp [N]
      nlinarith [Real.sin_sq_add_cos_sq z]
    linarith

lemma sideSide_margin_nonneg {w : ℝ}
    (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    0 ≤ (sideSideL w)^2-targetSq*sideSideRadicand w := by
  by_cases h : w = 0
  · subst w
    norm_num [sideSideL, sideSideRadicand, targetSq]
  · exact (sideSide_margin_pos hw h).le

lemma sideSideL_ge_norm {w : ℝ} (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    radius*Real.sqrt (sideSideRadicand w) ≤ sideSideL w := by
  have hrad : 0 ≤ sideSideRadicand w := by unfold sideSideRadicand; positivity
  have hs := Real.sq_sqrt hrad
  have hL := sideSideL_pos hw
  have hm := sideSide_margin_nonneg hw
  have hnorm : 0 ≤ radius*Real.sqrt (sideSideRadicand w) :=
    mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
  have he : (radius*Real.sqrt (sideSideRadicand w))^2=targetSq*sideSideRadicand w := by
    rw [mul_pow, radius_sq, hs]
    rfl
  nlinarith

def sideSideSupport (a u A v w : ℝ) : ℝ :=
  1/2-u+A*Real.sin w-v*Real.cos w+(|Real.sin w|+Real.cos w)/2

lemma sideSide_support_identity {a u A v w : ℝ}
    (hw : w = side a u+side A v-gap) :
    sideSideSupport a u A v w = sideSideL w+39/20 +
      ((-9/10)*(a+1/2)+(-3/5)*(u+1/2)) +
      (Real.sin w-9/10)*(A+1/2)+(2/5-Real.cos w)*(v+1/2) := by
  unfold sideSideSupport sideSideL
  rw [abs_min_identity]
  dsimp [side, gap] at hw
  nlinarith

private lemma fixed_dual_norm :
    radius*Real.sqrt (((-9/10 : ℝ)^2+(-3/5)^2)) = 39/20 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (-9/10)^2+(-3/5)^2 by norm_num)
  have hn : 0 ≤ radius*Real.sqrt (((-9/10 : ℝ)^2+(-3/5)^2)) :=
    mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
  have he : (radius*Real.sqrt (((-9/10 : ℝ)^2+(-3/5)^2)))^2=(39/20 : ℝ)^2 := by
    rw [mul_pow, radius_sq, hs]
    norm_num
  nlinarith

lemma sideSide_support_nonneg {a u A v w : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hw : w = side a u+side A v-gap)
    (hrange : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    0 ≤ sideSideSupport a u A v w := by
  have hfirst := dot_lower_candidate (p := -9/10) (r := -3/5) h.2.2.2
  have hsecond := dot_lower_candidate (p := Real.sin w-9/10)
    (r := 2/5-Real.cos w) h'.2.2.2
  have hnorm := sideSideL_ge_norm hrange
  rw [show -radius*Real.sqrt (((-9/10 : ℝ)^2+(-3/5)^2)) = -(39/20) by
    nlinarith [fixed_dual_norm]] at hfirst
  change -radius*Real.sqrt (sideSideRadicand w) ≤ _ at hsecond
  rw [sideSide_support_identity hw]
  linarith

/-- Strict containment of the first side state makes this sector strictly positive. -/
theorem sideSide_support_pos {a u A v : ℝ}
    (h : StrictlyAdmissible a u) (h' : Admissible A v)
    (hsel : label a u = side a u) (hsel' : label A v = side A v) :
    0 < sideSideSupport a u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : w = side a u+side A v-gap := by simp only [w,hsel,hsel']
  have hrange : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := by
    have h0 := h.admissible.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.admissible.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  have hfirst : -(39/20 : ℝ) < (-9/10)*(a+1/2)+(-3/5)*(u+1/2) := by
    have hid : ((-9/10)*(a+1/2)+(-3/5)*(u+1/2))^2+
        ((-9/10)*(u+1/2)-(-3/5)*(a+1/2))^2 = (117/100)*phi a u := by
      dsimp [phi]
      ring
    have hp := h.2.2.2
    dsimp [targetSq] at hp
    nlinarith [sq_nonneg ((-9/10)*(u+1/2)-(-3/5)*(a+1/2))]
  have hsecond := dot_lower_candidate (p := Real.sin w-9/10)
    (r := 2/5-Real.cos w) h'.2.2.2
  change -radius*Real.sqrt (sideSideRadicand w) ≤ _ at hsecond
  have hnorm := sideSideL_ge_norm hrange
  change 0 < sideSideSupport a u A v w
  rw [sideSide_support_identity hw]
  linarith

end SquaresInCircles.Seven
