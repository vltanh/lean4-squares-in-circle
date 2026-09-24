import SquaresInCircles.Seven.SmallAndParallelGaps

/-!
# Parallel squares with closed containment

The parallel-label inequalities of the lower bound, with the tangent
remainders allowed to vanish, for gaps below `π/3`.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

lemma opposite_labels_ge {a x A y : ℝ}
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

lemma quarter_difference_horizontal_le {a b A B : ℝ}
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

lemma quarter_difference_le {a b A B : ℝ}
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

lemma parallel_zero_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 < g ∧ g < gap)
    (he : g+s.coe*label a u-t.coe*label A v = 0) :
    0 < pairSupport a u A v s t k g := by
  have hang : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v =
      cardinalAngle k+Real.pi := by linarith
  rw [pairSupport,hang,support_add_pi,cardinal_support_sum]
  have h0 := h.label_nonneg
  have h1 := h'.label_nonneg
  have ha := h.a_lt_five_fourths
  have hA := h'.a_lt_five_fourths
  have hu := h.u_lt
  have hv := h'.u_lt
  fin_cases k
  · norm_num
    linarith [h.2.2.1]
  · by_contra hn
    cases s <;> cases t <;> norm_num [TransverseSign.coe] at hn he ⊢
    · linarith [h.1]
    · linarith [h.1,h'.1]
    · have hl := opposite_labels_ge h h' (show 1 ≤ u+v by linarith)
      linarith [hg.2]
    · linarith [h'.1]
  · norm_num
    linarith [h'.2.2.1]
  · cases s <;> cases t <;> norm_num [TransverseSign.coe] at he ⊢
    · linarith [h'.1]
    · linarith [hg.1]
    · linarith [h.1,h'.1]
    · linarith [h.1]

lemma parallel_quarter_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 < g ∧ g < gap)
    (he : g+s.coe*label a u-t.coe*label A v = Real.pi/2) :
    0 < pairSupport a u A v s t k g := by
  have hang : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v =
      cardinalAngle k+Real.pi/2 := by linarith
  rw [pairSupport,hang,support_add_half_pi,cardinal_support_sum]
  have hu : |s.coe*u| < 31/40 := by
    cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.1] using h.u_lt
  have hv : |t.coe*v| < 31/40 := by
    cases t <;> simpa [TransverseSign.coe,abs_of_nonneg h'.1] using h'.u_lt
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  have hlabel (hh : 1 ≤ a+t.coe*v ∨ 1 ≤ A-s.coe*u) : False := by
    have hp := quarter_difference_le (sign_admissible h s) (sign_admissible h' t) hh
    rw [sign_label h s,sign_label h' t] at hp
    dsimp [gap] at hg
    linarith
  fin_cases k
  · norm_num
    linarith [h.2.2.1]
  · by_contra hn
    norm_num at hn
    exact hlabel (Or.inr (by linarith))
  · by_contra hn
    norm_num at hn
    exact hlabel (Or.inl (by linarith))
  · norm_num
    linarith [h'.2.2.1]

lemma cardinal_target_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 1 ≤ g ∧ g < gap)
    (hcard : Real.sin (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v) = 0 ∨
      Real.cos (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v) = 0) :
    0 < pairSupport a u A v s t k g := by
  let d := g+s.coe*label a u-t.coe*label A v
  have hr : -Real.pi/2 < d ∧ d < Real.pi := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    cases s <;> cases t <;> dsimp [d,gap,TransverseSign.coe] at * <;>
      constructor <;> linarith [Real.pi_pos]
  have he : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v =
      cardinalAngle k+Real.pi-d := by dsimp [d]; ring
  rw [he] at hcard
  rcases cardinal_target_relative k hcard with hsin | hcos
  · have hd := sin_zero_between ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩ hsin
    exact parallel_zero_pos_below s t k h h' ⟨by linarith [hg.1],hg.2⟩ hd
  · have hd := cos_zero_between hr hcos
    exact parallel_quarter_pos_below s t k h h' ⟨by linarith [hg.1],hg.2⟩ hd

end Equality
end SquaresInCircles.Seven
