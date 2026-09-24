import SquaresInCircles.Seven.Uniqueness.ContactTypes
import SquaresInCircles.Seven.FixedGap

/-!
# Zero sets of the non-strict support inequalities

Positive sectors are already excluded by the optimality draft. Here we retain
the remainders in the sectors that may vanish. These are proofs about the
original coordinates, not only about endpoints used in their minimization.
-/
noncomputable section
namespace SquaresInCircles.Seven.Uniqueness
open Boundary

lemma sideSide_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hT' : label A v=side A v)
    (hzero : pairSupport a u A v .negative .positive 1 gap=0) :
    a=1 ∧ u=1/2 ∧ A=1 ∧ v=1/2 := by
  let w := label a u+label A v-gap
  have hw : w=side a u+side A v-gap := by simp [w,hT,hT']
  have hr : -Real.pi/3≤w ∧ w≤Real.pi/6 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  rw [pairSupport_forward_opposite h h'] at hzero
  change sideSideSupport a u A v w=0 at hzero
  have hw0 : w=0 := by
    by_contra hn
    have hm := sideSide_margin_pos hr hn
    have hL := sideSideL_pos hr
    have hrad : 0≤sideSideRadicand w := by unfold sideSideRadicand; positivity
    have hs := Real.sq_sqrt hrad
    have hn0 : 0≤radius*Real.sqrt (sideSideRadicand w) :=
      mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
    have he : (radius*Real.sqrt (sideSideRadicand w))^2=
        targetSq*sideSideRadicand w := by
      rw [mul_pow,radius_sq,hs]
      rfl
    have hstrict : radius*Real.sqrt (sideSideRadicand w)<sideSideL w := by
      nlinarith
    have hfirst : -(39/20 : ℝ)≤(-9/10)*(a+1/2)+(-3/5)*(u+1/2) := by
      linarith [h.tangent]
    have hsecond := dot_lower_candidate (p := Real.sin w-9/10)
      (r := 2/5-Real.cos w) h'.2.2.2
    change -radius*Real.sqrt (sideSideRadicand w)≤_ at hsecond
    rw [sideSide_support_identity hw] at hzero
    linarith
  have hs : 1≤u+v := by
    rw [hw0] at hzero
    norm_num [sideSideSupport] at hzero
    linarith
  have he : label a u+label A v=gap := by
    dsimp [w] at hw0
    linarith
  obtain ⟨⟨ha,hu⟩,⟨hA,hv⟩⟩ := opposite_labels_eq h h' hs he
  exact ⟨ha,hu,hA,hv⟩

lemma forward_negative_zero {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u)
    (htarget : ActiveLabel A v)
    (hzero : pairSupport a u A v sgn .negative 1 gap=0) :
    u=0 ∧ A=1 ∧ v=1/2 := by
  let r := sgn.coe*label a u
  let e := r+label A v-Real.pi/6
  have hlow := forward_negative_target_lower sgn h h' hsource
  change 1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2≤_ at hlow
  rw [hzero] at hlow
  have he : -Real.pi/2≤e ∧ e≤Real.pi/3 := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    cases sgn <;> dsimp [e,r,TransverseSign.coe] <;>
      constructor <;> linarith [Real.pi_pos]
  rcases htarget with hA | hT
  · have hp := negative_target_axial_pos h' hA he rfl
    change 0<1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2 at hp
    exact False.elim (by linarith)
  · have he' : -1<e := by
      have hs := side_selected_label_gt h' hT
      have ht0 := h.label_nonneg
      have ht1 := h.label_le_quarter
      cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> linarith [pi_upper_22]
    have hid :
        1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2=
        sideTarget A v e := by
      have hr : e=r+side A v-Real.pi/6 := by simp [e,hT]
      rw [side_identity_radial] at hr
      dsimp [sideTarget]
      nlinarith
    rw [hid] at hlow
    have he0 : 0≤e := by
      by_contra hn
      have hp := sideTarget_negative_pos h' hT (z := -e)
        ⟨by linarith,by linarith⟩
      simp only [neg_neg] at hp
      linarith
    have hp := sideTarget_positive_angle h' ⟨he0,he.2⟩
    have hw : remainder A v=0 := by linarith [h'.remainder_nonneg]
    have heq : e=0 := by linarith [h'.remainder_nonneg]
    obtain ⟨hA,hv⟩ := (remainder_zero_iff h').mp hw
    have hr : r=0 := by
      dsimp [e] at heq
      rw [hA,hv,side_contact_label] at heq
      linarith
    have hlabel : label a u=0 := by
      cases sgn <;> simpa [r,TransverseSign.coe] using hr
    exact ⟨h.label_zero_iff.mp hlabel,hA,hv⟩

lemma inward_opposite_side_axial_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (hzero : pairSupport a u A v .positive .negative 2 gap=0) :
    a=1 ∧ u=1/2 ∧ v=0 := by
  have he : label a u+label A v-Real.pi/6≤0 := by
    by_contra hn
    have hp := inward_opposite_side_positive_turn h h' hT hA (lt_of_not_ge hn)
    rw [hzero] at hp
    exact False.elim ((lt_irrefl 0) hp)
  have hb := inward_opposite_negative_turn h h' hT hA he
  rw [hzero] at hb
  have hw : remainder a u=0 := by
    linarith [h.remainder_nonneg,abs_nonneg (label a u+label A v-Real.pi/6)]
  have heq : label a u+label A v-Real.pi/6=0 := by
    apply abs_eq_zero.mp
    linarith [h.remainder_nonneg,abs_nonneg (label a u+label A v-Real.pi/6)]
  obtain ⟨ha,hu⟩ := (remainder_zero_iff h).mp hw
  have hv : v=0 := by
    rw [ha,hu,side_contact_label,hA] at heq
    dsimp [axial] at heq
    linarith
  exact ⟨ha,hu,hv⟩

lemma inward_opposite_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v)
    (hzero : pairSupport a u A v .positive .negative 2 gap=0) :
    a=1 ∧ u=1/2 ∧ v=0 := by
  have targetAxial (B w : ℝ) (hB : Admissible B w)
      (hBA : label B w=axial w)
      (he : pairSupport a u B w .positive .negative 2 gap=0) :
      a=1 ∧ u=1/2 ∧ w=0 := by
    rcases ha with hA | hT
    · have hp := inward_opposite_axial_axial_pos h hB hA hBA
      rw [he] at hp
      exact False.elim ((lt_irrefl 0) hp)
    · exact inward_opposite_side_axial_zero h hB hT hBA he
  rcases hb with hA | hT
  · exact targetAxial A v h' hA hzero
  · let s := label A v
    have hs : s0≤s ∧ s≤Real.pi/4 :=
      ⟨(side_state_transition_bounds h' hT).2.2,h'.label_le_quarter⟩
    obtain ⟨hB,hlabel,hside⟩ := tie_state hs
    have hBA : label (tieA s) ((4/5)*s)=axial ((4/5)*s) := by
      rw [hlabel]
      dsimp [axial]
      ring
    have hcomp := inward_opposite_side_target_reduction h h' hT
    have hnon := fixed_gap_nonneg .positive .negative 2 h hB
    rw [hzero] at hcomp
    have he : pairSupport a u (tieA s) ((4/5)*s) .positive .negative 2 gap=0 := by
      linarith
    have hz := (targetAxial _ _ hB hBA he).2.2
    have hp : 0<s := lt_trans (by norm_num) (side_selected_label_gt h' hT)
    exact False.elim (by linarith)

end SquaresInCircles.Seven.Uniqueness
