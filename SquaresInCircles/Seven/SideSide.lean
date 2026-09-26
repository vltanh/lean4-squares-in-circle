import SquaresInCircles.Seven.Contacts
import SquaresInCircles.Seven.TaylorBounds

/-!
# Two side labels

The support sum of two side-selected squares with opposite signs on the
forward axis, bounded below by a Cauchy–Schwarz certificate over the whole
admissible region. The certificate is tight only at zero turn, so the sum
vanishes only at two side states.
-/
noncomputable section
namespace SquaresInCircles.Seven

private lemma abs_min_identity (x : ℝ) : |x| = x-2*min x 0 := by
  by_cases h : 0 ≤ x
  · rw [abs_of_nonneg h, min_eq_right h]; ring
  · rw [abs_of_nonpos (le_of_not_ge h), min_eq_left (le_of_not_ge h)]; ring

def sideSideL (w : ℝ) : ℝ :=
  19/20+Real.cos w-min (Real.sin w) 0-(6/5)*w

def sideSideRadicand (w : ℝ) : ℝ :=
  (Real.sin w-9/10)^2+(2/5-Real.cos w)^2

lemma cos_ge_half {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    (1/2 : ℝ) ≤ Real.cos z := by
  simpa only [Real.cos_pi_div_three] using
    Real.cos_le_cos_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos]) hz.2

/-- The turn of two labels on the forward axis with signs `(-, +)`. -/
lemma forward_turn_range {a u A v : ℝ} (h : Admissible a u) (h' : Admissible A v) :
    -Real.pi/3 ≤ label a u+label A v-gap ∧ label a u+label A v-gap ≤ Real.pi/6 := by
  have h0 := h.label_nonneg
  have h1 := h'.label_nonneg
  have h2 := h.label_le_quarter
  have h3 := h'.label_le_quarter
  dsimp [gap]
  constructor <;> linarith

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
      linarith [Real.sin_sq_le_sq (x := w), Real.sin_sq_add_cos_sq w]
    have hpoly :
        w*(468-724*w+90*w^2-40*w^4) ≤
        (19+20*Real.cos w-24*w)^2-
          13*(197-180*Real.sin w-80*Real.cos w) := by
      linarith
    have hw4 : w^4 ≤ (8/15 : ℝ)^4 := by gcongr
    have hp : 0 < 468-724*w+90*w^2-40*w^4 := by
      linarith [sq_nonneg w]
    have hn := mul_pos h hp
    have hid :
        400*((sideSideL w)^2-targetSq*sideSideRadicand w) =
        (19+20*Real.cos w-24*w)^2-
          13*(197-180*Real.sin w-80*Real.cos w) := by
      unfold sideSideL sideSideRadicand targetSq
      rw [min_eq_right hs0]
      linear_combination (-1300)*Real.sin_sq_add_cos_sq w
    linarith
  · let z := -w
    have hz : 0 < z := by dsimp [z]; linarith [lt_of_le_of_ne (not_lt.mp h) hne]
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
      linarith
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
      linear_combination (-900)*Real.sin_sq_add_cos_sq z
    linarith

lemma sideSide_margin_nonneg {w : ℝ}
    (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    0 ≤ (sideSideL w)^2-targetSq*sideSideRadicand w := by
  by_cases h : w = 0
  · subst w
    norm_num [sideSideL, sideSideRadicand, targetSq]
  · exact (sideSide_margin_pos hw h).le

private lemma norm_sq (w : ℝ) :
    (radius*Real.sqrt (sideSideRadicand w))^2=targetSq*sideSideRadicand w := by
  have hrad : 0 ≤ sideSideRadicand w := by unfold sideSideRadicand; positivity
  rw [mul_pow, radius_sq, Real.sq_sqrt hrad]
  rfl

lemma sideSideL_ge_norm {w : ℝ} (hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6) :
    radius*Real.sqrt (sideSideRadicand w) ≤ sideSideL w := by
  have hL := sideSideL_pos hw
  have hm := sideSide_margin_nonneg hw
  have hnorm : 0 ≤ radius*Real.sqrt (sideSideRadicand w) :=
    mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
  nlinarith [norm_sq w]

def sideSideSupport (u A v w : ℝ) : ℝ :=
  1/2-u+A*Real.sin w-v*Real.cos w+(|Real.sin w|+Real.cos w)/2

lemma sideSide_support_identity {a u A v w : ℝ}
    (hw : w = side a u+side A v-gap) :
    sideSideSupport u A v w = sideSideL w+39/20 +
      ((-9/10)*(a+1/2)+(-3/5)*(u+1/2)) +
      (Real.sin w-9/10)*(A+1/2)+(2/5-Real.cos w)*(v+1/2) := by
  unfold sideSideSupport sideSideL
  rw [abs_min_identity]
  dsimp [side, gap] at hw
  linear_combination (6/5)*hw

private lemma fixed_dual_norm :
    radius*Real.sqrt (((-9/10 : ℝ)^2+(-3/5)^2)) = 39/20 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (-9/10)^2+(-3/5)^2 by norm_num)
  refine (sq_eq_sq₀ (mul_nonneg radius_nonneg (Real.sqrt_nonneg _)) (by norm_num)).mp ?_
  rw [mul_pow,radius_sq,hs]
  norm_num

lemma sideSide_support_lower {a u A v w : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hw : w = side a u+side A v-gap) :
    sideSideL w-radius*Real.sqrt (sideSideRadicand w) ≤ sideSideSupport u A v w := by
  have hfirst := dot_lower_candidate (p := -9/10) (r := -3/5) h.2.2.2
  have hsecond := dot_lower_candidate (p := Real.sin w-9/10)
    (r := 2/5-Real.cos w) h'.2.2.2
  rw [neg_mul,fixed_dual_norm] at hfirst
  change -radius*Real.sqrt (sideSideRadicand w) ≤ _ at hsecond
  rw [sideSide_support_identity hw]
  linarith

lemma sideSide_support_nonneg {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hT' : label A v = side A v) :
    0 ≤ sideSideSupport u A v (label a u+label A v-gap) := by
  have hl := sideSide_support_lower (w := label a u+label A v-gap) h h' (by rw [hT,hT'])
  linarith [sideSideL_ge_norm (forward_turn_range h h')]

/-- The side–side sum vanishes only at two side states. -/
lemma Equality.side_side_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hT' : label A v = side A v)
    (hz : sideSideSupport u A v (label a u+label A v-gap) = 0) :
    Side a u ∧ Side A v := by
  let w := label a u+label A v-gap
  have hw : w = side a u+side A v-gap := by simp only [w,hT,hT']
  have hw0 : w = 0 := by
    by_contra hne
    have hr := forward_turn_range h h'
    have hm := sideSide_margin_pos hr hne
    have hL := sideSideL_pos hr
    have hl := sideSide_support_lower h h' hw
    have hnorm : 0 ≤ radius*Real.sqrt (sideSideRadicand w) :=
      mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
    change sideSideSupport u A v w = 0 at hz
    nlinarith [norm_sq w]
  change sideSideSupport u A v w = 0 at hz
  rw [hw0] at hz hw
  have huv : u+v = 1 := by norm_num [sideSideSupport] at hz; linarith
  have hrem : remainder a u+remainder A v = 0 := by
    unfold side gap at hw
    unfold remainder
    linarith
  exact ⟨remainder_zero h (by linarith [h.remainder_nonneg,h'.remainder_nonneg]),
    remainder_zero h' (by linarith [h.remainder_nonneg,h'.remainder_nonneg])⟩

end SquaresInCircles.Seven
