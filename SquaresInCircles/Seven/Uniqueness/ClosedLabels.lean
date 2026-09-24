import SquaresInCircles.Seven.ParallelLabels
import SquaresInCircles.Seven.MarkerSeparation

/-!
# Closed label inequalities and their contact remainders

Optimality used strict containment. Equality needs the same inequalities on the
closed state domain. The weak statements below are proved directly; they are
not obtained by replacing `<` by `≤` in an unproved geometric assertion.
-/
noncomputable section
namespace SquaresInCircles.Seven.Uniqueness

lemma remainder_zero_iff {a u : ℝ} (h : Admissible a u) :
    remainder a u=0 ↔ a=1 ∧ u=1/2 := by
  constructor
  · intro hw
    have he := remainder_identity a u
    have hs := h.slack_nonneg
    exact ⟨by nlinarith [sq_nonneg (u-1/2)],
      by nlinarith [sq_nonneg (a-1)]⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [remainder]

lemma side_contact_label : label 1 (1/2)=Real.pi/6 := by
  have hp0 := pi_lower_157
  have hp1 := pi_upper_22
  norm_num [label,axial,side]
  rw [min_eq_right (by linarith),min_eq_left (by linarith)]

lemma axial_contact_label {a : ℝ} (h : Admissible a 0) : label a 0=0 :=
  h.label_zero_iff.mpr rfl

lemma opposite_labels_ge {a x A y : ℝ}
    (h : Admissible a x) (h' : Admissible A y) (hs : 1≤x+y) :
    gap≤label a x+label A y := by
  rcases h.selected with hx | hx | hx <;>
    rcases h'.selected with hy | hy | hy
  · rw [hx,hy]; exact (axial_axial_sum_gt hs).le
  · rw [hx,hy]; exact (axial_side_sum_gt h' hs).le
  · rw [hx,hy,add_comm]
    exact (cap_axial_sum_gt h' hs).le
  · rw [hx,hy,add_comm]
    exact (axial_side_sum_gt h (by linarith)).le
  · rw [hx,hy,side_side_sum_identity]
    linarith [h.remainder_nonneg,h'.remainder_nonneg]
  · rw [hx,hy,add_comm]
    exact (cap_side_sum_gt h' h (by linarith)).le
  · rw [hx,hy]
    exact (cap_axial_sum_gt h (by linarith)).le
  · rw [hx,hy]
    exact (cap_side_sum_gt h h' hs).le
  · rw [hx,hy]
    dsimp [gap]
    linarith [Real.pi_pos]

/-- Equality in the same-frame transverse bound fixes both side contacts. -/
lemma opposite_labels_eq {a x A y : ℝ}
    (h : Admissible a x) (h' : Admissible A y) (hs : 1≤x+y)
    (he : label a x+label A y=gap) :
    (a=1 ∧ x=1/2) ∧ (A=1 ∧ y=1/2) := by
  rcases h.selected with hx | hx | hx <;>
    rcases h'.selected with hy | hy | hy
  · rw [hx,hy] at he
    exact False.elim ((ne_of_gt (axial_axial_sum_gt hs)) he)
  · rw [hx,hy] at he
    exact False.elim ((ne_of_gt (axial_side_sum_gt h' hs)) he)
  · rw [hx,hy,add_comm] at he
    exact False.elim ((ne_of_gt (cap_axial_sum_gt h' hs)) he)
  · rw [hx,hy,add_comm] at he
    exact False.elim ((ne_of_gt (axial_side_sum_gt h (by linarith))) he)
  · rw [hx,hy,side_side_sum_identity] at he
    have hw : remainder a x=0 := by
      linarith [h.remainder_nonneg,h'.remainder_nonneg]
    have hw' : remainder A y=0 := by
      linarith [h.remainder_nonneg,h'.remainder_nonneg]
    exact ⟨(remainder_zero_iff h).mp hw,(remainder_zero_iff h').mp hw'⟩
  · rw [hx,hy,add_comm] at he
    exact False.elim ((ne_of_gt (cap_side_sum_gt h' h (by linarith))) he)
  · rw [hx,hy] at he
    exact False.elim ((ne_of_gt (cap_axial_sum_gt h (by linarith))) he)
  · rw [hx,hy] at he
    exact False.elim ((ne_of_gt (cap_side_sum_gt h h' hs)) he)
  · rw [hx,hy] at he
    dsimp [gap] at he
    exact False.elim (by linarith [Real.pi_pos])

lemma quarter_horizontal_le {a b A B : ℝ}
    (h : Admissible a |b|) (h' : Admissible A |B|)
    (hsep : 1≤a+B) : signedLabel a b-signedLabel A B≤Real.pi/6 := by
  by_cases hB : 0≤B
  · by_cases hb : 0≤b
    · have hx : Admissible a b := by simpa [abs_of_nonneg hb] using h
      have hy : Admissible A B := by simpa [abs_of_nonneg hB] using h'
      simp only [signedLabel,if_neg (not_lt_of_ge hb),if_neg (not_lt_of_ge hB),
        abs_of_nonneg hb,abs_of_nonneg hB]
      rcases hy.selected with hA | hT | hcap
      · rw [hA]
        have hl := hx.label_le_side
        have ht := hx.tangent
        dsimp [side,axial] at hl ⊢
        linarith
      · rw [hT]
        linarith [hx.label_le_quarter,side_selected_gt_twelfth hy hT]
      · rw [hcap]
        linarith [hx.label_le_quarter,Real.pi_pos]
    · have hb' : b<0 := lt_of_not_ge hb
      have hx := signedLabel_nonpos h hb'
      have hy := signedLabel_nonneg h' hB
      linarith [Real.pi_pos]
  · have hB' : B<0 := lt_of_not_ge hB
    by_cases hb : 0≤b
    · have hx : Admissible a b := by simpa [abs_of_nonneg hb] using h
      have hy : Admissible A (-B) := by simpa [abs_of_neg hB'] using h'
      have hl := hx.label_le_side
      have hr := hy.label_le_axial
      have ht := hx.tangent
      simp only [signedLabel,if_neg (not_lt_of_ge hb),if_pos hB',
        abs_of_nonneg hb,abs_of_neg hB']
      dsimp [side,axial] at hl hr
      linarith
    · have hb' : b<0 := lt_of_not_ge hb
      have hx := signedLabel_nonpos h hb'
      have hr := h'.label_le_axial
      have ha := h.a_lt_five_fourths
      simp only [signedLabel,if_pos hB',abs_of_neg hB'] at *
      dsimp [axial] at hr
      linarith [pi_lower_157]

lemma quarter_difference_le {a b A B : ℝ}
    (h : Admissible a |b|) (h' : Admissible A |B|)
    (hsep : 1≤a+B ∨ 1≤A-b) :
    signedLabel a b-signedLabel A B≤Real.pi/6 := by
  rcases hsep with hh | hh
  · exact quarter_horizontal_le h h' hh
  · have hrev : Admissible A |(-B)| := by simpa using h'
    have hrev' : Admissible a |(-b)| := by simpa using h
    have hh' := quarter_horizontal_le hrev hrev' (by linarith : 1≤A+-b)
    rw [signedLabel_neg h',signedLabel_neg h] at hh'
    linarith

end SquaresInCircles.Seven.Uniqueness
