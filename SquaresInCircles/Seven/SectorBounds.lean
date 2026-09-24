import SquaresInCircles.Seven.PairModel
import SquaresInCircles.Seven.TaylorBounds

/-!
# Bounds shared by the mixed fixed-gap support sectors

This file contains no numerical evaluation tactic or interval oracle. All
constants are rational; the quadratic inequalities retain the original
containment remainder.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma pi_lower_157 : (157 : ℝ)/50 < Real.pi := by linarith [Real.pi_gt_d2]
lemma pi_upper_22 : Real.pi < (22 : ℝ)/7 := by linarith [Real.pi_lt_d4]
lemma sqrt_three_bounds : (173 : ℝ)/100 < Real.sqrt 3 ∧ Real.sqrt 3 < 1733/1000 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]
lemma radius_lt_181 : radius < (181 : ℝ)/100 := by
  nlinarith [radius_sq, radius_nonneg]

lemma side_selected_label_gt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : (9 : ℝ)/25 < label a u := by
  let t := label a u
  have ht0 : 0 ≤ t := h.label_nonneg
  have htu : (4/5)*t ≤ u := by
    have ht := h.label_le_axial
    dsimp [axial] at ht
    dsimp [t]
    linarith
  have he : 9*a-4*u = 2*Real.pi+7-12*t := by
    dsimp [t] at *
    rw [hsel]
    dsimp [side]
    ring
  by_contra hn
  have ht1 : t ≤ 9/25 := le_of_not_gt hn
  have ha : 332/225-(44/45)*t < a := by linarith [pi_lower_157]
  have hp := h.2.2.2
  dsimp [phi,targetSq] at hp
  have hsqA := sq_nonneg (a-(332/225-(44/45)*t))
  have hsqU := sq_nonneg (u-(4/5)*t)
  have hlinA := mul_nonneg
    (show 0 ≤ a-(332/225-(44/45)*t) by linarith)
    (show 0 ≤ 2*(332/225-(44/45)*t)+1 by linarith)
  have hlinU := mul_nonneg
    (show 0 ≤ u-(4/5)*t by linarith)
    (show 0 ≤ 2*(4/5)*t+1 by linarith)
  have hquad := mul_nonneg (show 0 ≤ 9/25-t by linarith)
    (show 0 ≤ 139744/50625-(3232/2025)*(t+9/25) by linarith)
  nlinarith

lemma side_selected_a_gt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) : (7 : ℝ)/10 < a := by
  have ht := h.label_le_axial
  have hq := h.label_le_quarter
  rw [hsel] at ht hq
  dsimp [side,axial] at ht hq
  linarith [pi_upper_22]

lemma axial_tangent {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = axial u) : 9*a+11*u ≤ 2*Real.pi+7 := by
  have hh := h.label_le_side
  rw [hsel] at hh
  dsimp [side,axial] at hh
  linarith

lemma axial_sum_lt {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = axial u) : a+u < (113 : ℝ)/80 := by
  have ht := axial_tangent h hsel
  by_contra hn
  have hs : 113/80 ≤ a+u := le_of_not_gt hn
  have hu : u < 23/80 := by linarith [pi_upper_22]
  have hp := h.2.2.2
  dsimp [phi,targetSq] at hp
  nlinarith [sq_nonneg (a-9/8),sq_nonneg (u-23/80)]

lemma side_remainder_quadratic {a u : ℝ} (h : Admissible a u)
    (hsel : label a u = side a u) :
    (9/5)*(label a u-Real.pi/6)^2 ≤ remainder a u := by
  let D := label a u-Real.pi/6
  let W := remainder a u
  have hW : 0 ≤ W := h.remainder_nonneg
  have hD : D ≤ 4/15 := by
    have hh := h.label_le_quarter
    dsimp [D]
    linarith [pi_upper_22]
  have hx : a-1 = -(4/5)*D-(2/15)*W := by
    have hh := side_identity_radial a u
    rw [← hsel] at hh
    dsimp [D,W]
    linarith
  have hy : u-1/2 = (6/5)*D-(3/10)*W := by
    have hh := side_identity_transverse a u
    rw [← hsel] at hh
    dsimp [D,W]
    linarith
  have hs : (a-1)^2+(u-1/2)^2 ≤ W := by
    have hh := remainder_identity a u
    have hp := h.slack_nonneg
    dsimp [W]
    linarith
  have hid : (a-1)^2+(u-1/2)^2 =
      (52/25)*D^2-(38/75)*D*W+(97/900)*W^2 := by
    rw [hx,hy]
    ring
  have hprod := mul_nonneg hW (show 0 ≤ 4/15-D by linarith)
  change (9/5)*D^2 ≤ W
  nlinarith [sq_nonneg W,sq_nonneg D]

lemma cos_nonneg_quarter {x : ℝ} (hx : -Real.pi/2 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc hx

lemma sin_le_sin_half {x y : ℝ}
    (hx : -Real.pi/2 ≤ x ∧ x ≤ Real.pi/2)
    (hy : -Real.pi/2 ≤ y ∧ y ≤ Real.pi/2) (hxy : x ≤ y) :
    Real.sin x ≤ Real.sin y := Real.strictMonoOn_sin.monotoneOn hx hy hxy

lemma cos_le_sin_of_quarter {x : ℝ}
    (hx : Real.pi/4 ≤ x ∧ x ≤ Real.pi/2) : Real.cos x ≤ Real.sin x := by
  have hh := sin_le_sin_half
    (x := Real.pi/2-x) (y := x)
    (by constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    (by constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    (by linarith [hx.1])
  simpa only [Real.sin_pi_div_two_sub] using hh

lemma sin_le_cos_of_small {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ Real.pi/4) : Real.sin x ≤ Real.cos x := by
  have hh := sin_le_sin_half (x := x) (y := Real.pi/2-x)
    (by constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    (by constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    (by linarith [hx.2])
  simpa only [Real.sin_pi_div_two_sub] using hh

lemma sin_add_cos_le_three_halves (x : ℝ) : Real.sin x+Real.cos x < 3/2 := by
  have hu := Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (Real.sin x-Real.cos x)]

lemma trig_sum_monotone : MonotoneOn (fun x : ℝ => Real.cos x+Real.sin x)
    (Icc 0 (Real.pi/4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by fun_prop)
  · intro x hx
    fun_prop
  · intro x hx
    have hm := interior_subset hx
    have hd : deriv (fun t : ℝ => Real.cos t+Real.sin t) x =
        Real.cos x-Real.sin x := by
      simp (disch := fun_prop)
      ring
    rw [hd]
    exact sub_nonneg.mpr (sin_le_cos_of_small hm)

lemma dot_upper_unit {X Y C S : ℝ}
    (hp : X^2+Y^2 ≤ targetSq) (hu : C^2+S^2=1) : X*C+Y*S ≤ radius := by
  have hi : (X*C+Y*S)^2+(X*S-Y*C)^2=(X^2+Y^2)*(C^2+S^2) := by ring
  rw [hu,mul_one] at hi
  have hr := radius_sq
  dsimp [targetSq] at hp
  nlinarith [sq_nonneg (X*S-Y*C),radius_nonneg]

/-- Rational source/target bounds for the forward-positive sector. -/
lemma forward_positive_profile {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 5/16) :
    radius < 1/2+(4/5)*t+Real.cos (Real.pi/6-t)+Real.sin (Real.pi/6-t) := by
  let f : ℝ → ℝ := fun x => 1/2+(4/5)*x+Real.cos (Real.pi/6-x)+Real.sin (Real.pi/6-x)
  have hmono : MonotoneOn f (Icc 0 (5/16)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by dsimp [f]; fun_prop)
    · intro x hx
      dsimp [f]
      fun_prop
    · intro x hx
      have hx' : 0 ≤ x ∧ x ≤ 5/16 := interior_subset hx
      have hz : 21/100 < Real.pi/6-x ∧ Real.pi/6-x ≤ Real.pi/2 := by
        constructor <;> linarith [hx'.1,hx'.2,pi_lower_157,Real.pi_pos]
      have hsin := sin_le_sin_half
        (x := 21/100) (y := Real.pi/6-x)
        (by constructor <;> linarith [pi_lower_157,Real.pi_pos])
        (by constructor <;> linarith [hz.1,hz.2,Real.pi_pos]) hz.1.le
      have hlow := Real.sin_ge_sub_cube (show (0 : ℝ) ≤ 21/100 by norm_num)
      have hd : deriv f x = 4/5+Real.sin (Real.pi/6-x)-Real.cos (Real.pi/6-x) := by
        simp (disch := fun_prop) [f]
        ring
      rw [hd]
      linarith [Real.cos_le_one (Real.pi/6-x)]
  have hh := hmono (by constructor <;> norm_num) ht ht.1
  have hstart : f 0 = 1+Real.sqrt 3/2 := by
    simp [f,Real.cos_pi_div_six,Real.sin_pi_div_six]
    ring
  rw [hstart] at hh
  change radius < f t
  linarith [sqrt_three_bounds.1,radius_lt_181]

end SquaresInCircles.Seven
