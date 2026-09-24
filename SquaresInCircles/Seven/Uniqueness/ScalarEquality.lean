import SquaresInCircles.Seven.FixedGap
import SquaresInCircles.Seven.CanonicalPair
import SquaresInCircles.Seven.Uniqueness.NormalForm

/-!
# Contacts

The three kinds of contact between labelled states, and the zeros of the
sector bounds: in each sector a zero forces a contact. A side state is
`(1, 1/2)`; an axial state `(a, 0)` keeps `a` free.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

abbrev Side (a u : ℝ) : Prop := a = 1 ∧ u = 1/2
abbrev Axial (a u : ℝ) : Prop := u = 0 ∧ 1/2 ≤ a ∧ a ≤ columnLimit

def OrderedContact (a u A v : ℝ) (s t : TransverseSign) : Prop :=
  (s = .negative ∧ t = .positive ∧ Side a u ∧ Side A v) ∨
  (s = .positive ∧ Side a u ∧ Axial A v) ∨
  (t = .negative ∧ Axial a u ∧ Side A v)

lemma remainder_zero {a u : ℝ} (h : Admissible a u)
    (hz : remainder a u = 0) : Side a u := by
  have he := remainder_identity a u
  have hs := h.slack_nonneg
  exact ⟨by nlinarith [sq_nonneg (u-1/2)],
    by nlinarith [sq_nonneg (a-1)]⟩

lemma axial_of_transverse_zero {a u : ℝ} (h : Admissible a u) (hu : u = 0) :
    Axial a u := ⟨hu,h.2.2.1,h.a_le_sqrt_three⟩

lemma side_label : label 1 (1/2) = Real.pi/6 := by
  have hp := pi_lt_22_over_7
  have hp0 := Real.pi_pos
  unfold label axial side
  rw [min_eq_right (a := (5*(1/2)/4 : ℝ)) (by linarith), min_eq_left (by linarith)]
  ring

lemma axial_label {a u : ℝ} (h : Admissible a u) (ha : Axial a u) :
    label a u = 0 := h.label_zero_iff.mpr ha.1

lemma side_neq_cap : label 1 (1/2) ≠ Real.pi/4 := by
  rw [side_label]
  linarith [Real.pi_pos]

lemma contact_label_not_cap {a u A v : ℝ} {s t : TransverseSign}
    (h : Admissible a u) (h' : Admissible A v)
    (hc : OrderedContact a u A v s t) :
    label a u ≠ Real.pi/4 ∧ label A v ≠ Real.pi/4 := by
  rcases hc with ⟨_,_,hs,ht⟩ | ⟨_,hs,ht⟩ | ⟨_,hs,ht⟩
  · simpa [hs.1,hs.2,ht.1,ht.2] using And.intro side_neq_cap side_neq_cap
  · rw [hs.1,hs.2,axial_label h' ht]
    exact ⟨side_neq_cap,by linarith [Real.pi_pos]⟩
  · rw [ht.1,ht.2,axial_label h hs]
    exact ⟨by linarith [Real.pi_pos],side_neq_cap⟩

lemma reflected_reverse_contact {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact A v a u t.flip s.flip) : OrderedContact a u A v s t := by
  cases s <;> cases t <;>
    simp only [OrderedContact,TransverseSign.flip] at hc ⊢ <;> aesop

private lemma dual_norm : radius * Real.sqrt ((-9/10 : ℝ)^2+(-3/5)^2) = 39/20 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (-9/10)^2+(-3/5)^2 by norm_num)
  have hn := mul_nonneg radius_nonneg (Real.sqrt_nonneg ((-9/10 : ℝ)^2+(-3/5)^2))
  have he : (radius * Real.sqrt ((-9/10 : ℝ)^2+(-3/5)^2))^2 = (39/20 : ℝ)^2 := by
    rw [mul_pow,radius_sq,hs]
    norm_num
  nlinarith

/-- The side–side bound of the forward sector vanishes only at two side
states. -/
lemma side_side_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hT' : label A v = side A v)
    (hz : sideSideSupport u A v (label a u+label A v-gap) = 0) :
    Side a u ∧ Side A v := by
  let w := label a u+label A v-gap
  have hw : w = side a u+side A v-gap := by simp [w,hT,hT']
  have hr : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  have hw0 : w = 0 := by
    by_contra hne
    have hm := sideSide_margin_pos hr hne
    have hL := sideSideL_pos hr
    have hfirst := dot_lower_candidate (p := -9/10) (r := -3/5) h.2.2.2
    have hsecond := dot_lower_candidate (p := Real.sin w-9/10)
      (r := 2/5-Real.cos w) h'.2.2.2
    have hd := dual_norm
    have hrad : 0 ≤ sideSideRadicand w := by unfold sideSideRadicand; positivity
    have hs := Real.sq_sqrt hrad
    have hn := mul_nonneg radius_nonneg (Real.sqrt_nonneg (sideSideRadicand w))
    have he : (radius * Real.sqrt (sideSideRadicand w))^2 =
        targetSq*sideSideRadicand w := by rw [mul_pow,radius_sq,hs]; rfl
    change -radius*Real.sqrt (sideSideRadicand w) ≤ _ at hsecond
    change sideSideSupport u A v w = 0 at hz
    rw [sideSide_support_identity hw] at hz
    have hl : sideSideL w ≤ radius * Real.sqrt (sideSideRadicand w) := by nlinarith
    have hp := mul_nonneg (sub_nonneg.mpr hl)
      (show 0 ≤ radius*Real.sqrt (sideSideRadicand w)+sideSideL w by linarith)
    nlinarith
  change sideSideSupport u A v w = 0 at hz
  rw [hw0] at hz
  have huv : u+v = 1 := by norm_num [sideSideSupport] at hz; linarith
  have hs : side a u+side A v = gap := by linarith [hw]
  have he := side_side_sum_identity a u A v
  have hrem : remainder a u+remainder A v = 0 := by rw [huv] at he; linarith
  exact ⟨remainder_zero h (by linarith [h.remainder_nonneg,h'.remainder_nonneg]),
    remainder_zero h' (by linarith [h.remainder_nonneg,h'.remainder_nonneg])⟩

/-- A zero of the inward sector with signs `(+, -)`, side and axial labels, is
a contact. -/
lemma inward_opposite_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v)
    (hz : pairSupport a u A v .positive .negative 2 gap = 0) :
    Side a u ∧ Axial A v := by
  by_cases he : 0 < label a u+label A v-Real.pi/6
  · have hp := inward_opposite_side_positive_turn h h' hT hA he
    rw [hz] at hp
    exact False.elim ((lt_irrefl (0 : ℝ)) hp)
  · have hl := inward_opposite_negative_turn h h' hT hA (le_of_not_gt he)
    rw [hz] at hl
    have hW : remainder a u = 0 := by
      linarith [h.remainder_nonneg,abs_nonneg (label a u+label A v-Real.pi/6)]
    have hab : label a u+label A v-Real.pi/6 = 0 :=
      abs_eq_zero.mp (by
        linarith [h.remainder_nonneg,abs_nonneg (label a u+label A v-Real.pi/6)])
    have hc := remainder_zero h hW
    have hv : v = 0 := by
      rw [hc.1,hc.2,side_label,hA] at hab
      dsimp [axial] at hab
      linarith
    exact ⟨hc,axial_of_transverse_zero h' hv⟩

/-- The inward sector with signs `(+, -)` has no zero with a side label on
the second square. -/
lemma inward_side_target_ne_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (ha : ActiveLabel a u)
    (hT : label A v = side A v)
    (hz : pairSupport a u A v .positive .negative 2 gap = 0) : False := by
  let s := label A v
  have hs : Boundary.s0 ≤ s ∧ s ≤ Real.pi/4 :=
    ⟨(Boundary.side_state_transition_bounds h' hT).2.2,h'.label_le_quarter⟩
  obtain ⟨hb,hlab,hside⟩ := Boundary.tie_state hs
  have hA : label (Boundary.tieA s) ((4/5)*s) = axial ((4/5)*s) := by
    rw [hlab]
    dsimp [axial]
    ring
  have hcomp := inward_opposite_side_target_reduction h h' hT
  have hnn := fixed_gap_nonneg .positive .negative 2 h hb
  have htie : pairSupport a u (Boundary.tieA s) ((4/5)*s) .positive .negative 2 gap = 0 := by
    linarith
  rcases ha with hsourceA | hsourceT
  · have hp := inward_opposite_axial_axial_pos h hb hsourceA hA
    rw [htie] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  · have hc := inward_opposite_zero h hb hsourceT hA htie
    have hpos := side_selected_label_gt h' hT
    change 9/25 < s at hpos
    linarith [hc.2.1]

/-- The lower bound of the forward sector with `t = -1`, in the turn `e` and
the signed source label `r`. -/
def forwardRaw (A v e r : ℝ) : ℝ :=
  1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2

lemma forward_negative_target_zero {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn = .positive ∨ label a u = axial u)
    (hb : ActiveLabel A v)
    (hz : pairSupport a u A v sgn .negative 1 gap = 0) :
    Axial a u ∧ Side A v := by
  let e := sgn.coe*label a u+label A v-Real.pi/6
  let r := sgn.coe*label a u
  have he : e = r+label A v-Real.pi/6 := rfl
  have hrange : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3 := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    cases sgn <;> dsimp [e,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  have hl := forward_negative_target_lower sgn h h' hsource
  change forwardRaw A v e r ≤ _ at hl
  rw [hz] at hl
  rcases hb with hA | hT
  · have hp := negative_target_axial_pos h' hA hrange he
    change 0 < forwardRaw A v e r at hp
    linarith
  · have heL : -1 < e := by
      have hs := side_selected_label_gt h' hT
      cases sgn <;> dsimp [e,TransverseSign.coe] <;>
        linarith [h.label_nonneg,h.label_le_quarter,pi_lt_22_over_7]
    have hid : forwardRaw A v e r = sideTarget A v e := by
      rw [hT,side_identity_radial] at he
      dsimp [forwardRaw,sideTarget]
      nlinarith
    rw [hid] at hl
    have he0 : 0 ≤ e := by
      by_contra hn
      have hp := sideTarget_negative_pos h' hT
        (z := -e) ⟨by linarith,by linarith⟩
      simp only [neg_neg] at hp
      linarith
    have hbound := sideTarget_positive_angle h' ⟨he0,hrange.2⟩
    have hW : remainder A v = 0 := by linarith [h'.remainder_nonneg]
    have ez : e = 0 := by linarith [h'.remainder_nonneg]
    have hc := remainder_zero h' hW
    have ht : label a u = 0 := by
      rw [hc.1,hc.2,side_label] at he
      cases sgn <;> dsimp [r,TransverseSign.coe] at he <;> linarith
    exact ⟨axial_of_transverse_zero h (h.label_zero_iff.mp ht),hc⟩

end Equality
end SquaresInCircles.Seven
