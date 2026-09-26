import SquaresInCircles.Seven.Labels

/-!
# Labels of parallel squares

For parallel squares on opposite sides of the axis, and for quarter-turned
squares separated by a whole side, the labels are too far apart for a gap
below `π/3`.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma side_side_sum_identity (a x A y : ℝ) :
    side a x + side A y = gap + (5/6)*(x+y-1) +
      (remainder a x + remainder A y)/4 := by
  unfold side gap remainder
  ring

lemma axial_side_sum_gt {x A y : ℝ} (h' : Admissible A y) (hs : 1 ≤ x+y) :
    gap < axial x + side A y := by
  have hl : (11/12)*y+(3/4)*A < 31/24 := by
    linarith [h'.sum_lt, h'.2.1]
  dsimp [gap, axial, side]
  linarith [pi_lt_22_over_7]

lemma axial_axial_sum_gt {x y : ℝ} (hs : 1 ≤ x+y) :
    gap < axial x + axial y := by
  dsimp [gap, axial]
  linarith [pi_lt_22_over_7]

lemma cap_axial_sum_gt {x A y : ℝ}
    (h' : Admissible A y) (hs : 1 ≤ x+y) :
    gap < Real.pi/4 + axial x := by
  have hx : 9/40 < x := by linarith [h'.u_lt]
  dsimp [gap, axial]
  linarith [pi_lt_22_over_7]

lemma cap_side_sum_gt {a x A y : ℝ}
    (h : Admissible a x) (h' : Admissible A y) (hs : 1 ≤ x+y) :
    gap < Real.pi/4 + side A y := by
  have hy : 9/40 < y := by linarith [h.u_lt]
  rw [side_identity_transverse]
  have hw := h'.remainder_nonneg
  dsimp [gap]
  linarith [pi_lower_157]

/-- Two labels on opposite sides of parallel squares add up to at least
`π/3`. -/
theorem Equality.opposite_labels_ge {a x A y : ℝ}
    (h : Admissible a x) (h' : Admissible A y) (hs : 1 ≤ x+y) :
    gap ≤ label a x+label A y := by
  rcases h.selected with hx | hx | hx <;> rcases h'.selected with hy | hy | hy
  · rw [hx,hy]; exact (axial_axial_sum_gt hs).le
  · rw [hx,hy]; exact (axial_side_sum_gt h' hs).le
  · rw [hx,hy,add_comm]; exact (cap_axial_sum_gt h' hs).le
  · rw [hx,hy,add_comm]; exact (axial_side_sum_gt h (by linarith)).le
  · rw [hx,hy,side_side_sum_identity]
    linarith [h.remainder_nonneg,h'.remainder_nonneg]
  · rw [hx,hy,add_comm]; exact (cap_side_sum_gt h' h (by linarith)).le
  · rw [hx,hy]; exact (cap_axial_sum_gt h (by linarith)).le
  · rw [hx,hy]; exact (cap_side_sum_gt h h' hs).le
  · rw [hx,hy]
    dsimp [gap]
    linarith [Real.pi_pos]

lemma signedLabel_nonneg {a b : ℝ} (h : Admissible a |b|) (hb : 0 ≤ b) :
    0 ≤ signedLabel a b := by
  simpa only [signedLabel, ite_eq_right (not_lt_of_ge hb)] using h.label_nonneg

lemma signedLabel_nonpos {a b : ℝ} (h : Admissible a |b|) (hb : b < 0) :
    signedLabel a b ≤ 0 := by
  simp only [signedLabel, ite_eq_left hb]
  linarith [h.label_nonneg]

/-- One horizontal-separator alternative for a quarter-turned pair. -/
theorem Equality.quarter_difference_horizontal_le {a b A B : ℝ}
    (h : Admissible a |b|) (h' : Admissible A |B|)
    (hsep : 1 ≤ a+B) : signedLabel a b-signedLabel A B ≤ Real.pi/6 := by
  by_cases hB : 0 ≤ B
  · by_cases hb : 0 ≤ b
    · have hx : Admissible a b := by simpa only [abs_of_nonneg hb] using h
      have hy : Admissible A B := by simpa only [abs_of_nonneg hB] using h'
      have ht := hx.tangent
      simp only [signedLabel,ite_eq_right (not_lt_of_ge hb),ite_eq_right (not_lt_of_ge hB),
        abs_of_nonneg hb,abs_of_nonneg hB]
      rcases hy.selected with hA | hT | hcap
      · rw [hA]
        have hl := hx.label_le_side
        dsimp [side,axial] at hl ⊢
        linarith
      · rw [hT]
        linarith [hx.label_le_quarter,side_selected_gt_twelfth hy hT]
      · rw [hcap]
        linarith [hx.label_le_quarter,Real.pi_pos]
    · linarith [signedLabel_nonpos h (lt_of_not_ge hb),signedLabel_nonneg h' hB,Real.pi_pos]
  · have hB' : B < 0 := lt_of_not_ge hB
    by_cases hb : 0 ≤ b
    · have hx : Admissible a b := by simpa only [abs_of_nonneg hb] using h
      have hy : Admissible A (-B) := by simpa only [abs_of_neg hB'] using h'
      have hl := hx.label_le_side
      have hr := hy.label_le_axial
      have ht := hx.tangent
      simp only [signedLabel,ite_eq_right (not_lt_of_ge hb),ite_eq_left hB',
        abs_of_nonneg hb,abs_of_neg hB']
      dsimp [side,axial] at hl hr
      linarith
    · have hx := signedLabel_nonpos h (lt_of_not_ge hb)
      have hr := h'.label_le_axial
      have ha := h.a_lt_five_fourths
      simp only [signedLabel,ite_eq_left hB',abs_of_neg hB'] at *
      dsimp [axial] at hr
      linarith [pi_lower_157]

/-- Either separating coordinate suffices for the quarter-turn label inequality. -/
theorem Equality.quarter_difference_le {a b A B : ℝ}
    (h : Admissible a |b|) (h' : Admissible A |B|)
    (hsep : 1 ≤ a+B ∨ 1 ≤ A-b) :
    signedLabel a b-signedLabel A B ≤ Real.pi/6 := by
  rcases hsep with hh | hh
  · exact quarter_difference_horizontal_le h h' hh
  · have hh' := quarter_difference_horizontal_le
      (a := A) (b := -B) (A := a) (B := -b)
      (by simpa using h') (by simpa using h) (by linarith)
    rw [signedLabel_neg h',signedLabel_neg h] at hh'
    linarith

end SquaresInCircles.Seven
