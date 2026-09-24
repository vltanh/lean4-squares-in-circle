import SquaresInCircles.Seven.InwardTurnBounds

/-!
# Inward radial source: positive signs, side/axial labels

This sector is global in the admissible centers and relative orientation.
The support expression is the actual `pairSupport` from `PairModel`, not a
new geometric assumption. Equality fixes the side contact but leaves the
axial radial coordinate free, as required by the sliding construction.

Uncompiled incremental proof draft.
-/
noncomputable section
namespace SquaresInCircles.Seven

private def inwardExpression (A v e W : ℝ) : ℝ :=
  (4/5)*e+(2/15)*W-A*Real.sin e+|Real.sin e|/2+
    (v-1/2)*(1-Real.cos e)

lemma inward_side_axial_angle {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) :
    -Real.pi/3 ≤ label a u-label A v-Real.pi/6 ∧
      label a u-label A v-Real.pi/6 ≤ Real.pi/12 := by
  have ht := side_selected_gt_twelfth h hT
  rw [← hT] at ht
  have ht1 := h.label_le_quarter
  have hs0 := h'.label_nonneg
  have hs1 := h'.label_le_quarter
  constructor <;> linarith

private lemma inward_side_axial_identity {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    pairSupport a u A v .positive .positive 2 gap =
      inwardExpression A v (label a u-label A v-Real.pi/6) (remainder a u) := by
  let e := label a u-label A v-Real.pi/6
  have he : -Real.pi/3 ≤ e ∧ e ≤ Real.pi/12 :=
    inward_side_axial_angle h h' hT
  have hc : 0 ≤ Real.cos e := cos_nonneg_quarter
    ⟨by linarith [he.1,Real.pi_pos],by linarith [he.2,Real.pi_pos]⟩
  have hangle : 2*Real.pi-gap-label a u+label A v = 3*Real.pi/2-e := by
    dsimp [e,gap]
    ring
  have hcos : Real.cos (3*Real.pi/2-e) = -Real.sin e := by
    rw [show 3*Real.pi/2-e = (Real.pi+Real.pi/2)-e by ring]
    simp [Real.cos_sub,Real.cos_add,Real.sin_add]
  have hsin : Real.sin (3*Real.pi/2-e) = -Real.cos e := by
    rw [show 3*Real.pi/2-e = (Real.pi+Real.pi/2)-e by ring]
    simp [Real.sin_sub,Real.cos_add,Real.sin_add]
  have hlin : 1-a-v = (4/5)*e+(2/15)*remainder a u := by
    dsimp [e]
    rw [hT,hA]
    dsimp [side,axial,remainder]
    ring
  rw [pairSupport_two]
  simp only [TransverseSign.coe,one_mul]
  rw [hangle]
  change _ = inwardExpression A v e (remainder a u)
  simp only [support,hcos,hsin,abs_neg,abs_of_nonneg hc,inwardExpression]
  nlinarith

/-- The clearance lower bound needed when the relative turn is negative. -/
lemma inward_side_axial_transverse {a u A v z : ℝ}
    (h : Admissible a u)
    (hT : label a u = side a u) (hA : label A v = axial v)
    (he : label a u-label A v-Real.pi/6 = -z) :
    (4/5)*z-3/4 ≤ v-1/2 := by
  have ht := side_selected_gt_twelfth h hT
  rw [← hT] at ht
  rw [hA] at he
  dsimp [axial] at he
  linarith [pi_upper_22]

/-- Quantitative support bound; only the explicitly named labels are selected. -/
theorem inward_side_axial_lower {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    (2/15)*remainder a u+|label a u-label A v-Real.pi/6|/840 ≤
      pairSupport a u A v .positive .positive 2 gap := by
  let e := label a u-label A v-Real.pi/6
  have he := inward_side_axial_angle h h' hT
  change -Real.pi/3 ≤ e ∧ e ≤ Real.pi/12 at he
  rw [inward_side_axial_identity h h' hT hA]
  change (2/15)*remainder a u+|e|/840 ≤
    inwardExpression A v e (remainder a u)
  by_cases he0 : 0 ≤ e
  · have hh := inward_positive_turn_bound h'.a_le_sqrt_three h'.1 ⟨he0,he.2⟩
    rw [abs_of_nonneg he0]
    dsimp [inwardExpression]
    linarith
  · let z := -e
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by
      dsimp [z]
      constructor <;> linarith [he.1]
    have hez : e = -z := by dsimp [z]; ring
    have hv := inward_side_axial_transverse h hT hA hez
    have hh := inward_negative_turn_bound h'.2.2.1 hv hz
    rw [hez,abs_neg,abs_of_nonneg hz.1]
    dsimp [inwardExpression]
    nlinarith [hz.1]

lemma inward_side_axial_nonneg {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    0 ≤ pairSupport a u A v .positive .positive 2 gap := by
  have hh := inward_side_axial_lower h h' hT hA
  linarith [h.remainder_nonneg,abs_nonneg (label a u-label A v-Real.pi/6)]

/-- Strict containment of the side square is enough; the axial square may
slide and may already touch the candidate circle. -/
theorem inward_side_axial_pos {a u A v : ℝ}
    (h : StrictlyAdmissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    0 < pairSupport a u A v .positive .positive 2 gap := by
  have hh := inward_side_axial_lower h.admissible h' hT hA
  linarith [h.remainder_pos,abs_nonneg (label a u-label A v-Real.pi/6)]

/-- Zero support forces the side contact and zero transverse coordinate of
the axial square; no particular value of A is concluded. -/
theorem inward_side_axial_eq_zero {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v)
    (hzero : pairSupport a u A v .positive .positive 2 gap = 0) :
    a = 1 ∧ u = 1/2 ∧ v = 0 := by
  have hl := inward_side_axial_lower h h' hT hA
  rw [hzero] at hl
  have hw : remainder a u = 0 := by
    linarith [h.remainder_nonneg,abs_nonneg (label a u-label A v-Real.pi/6)]
  have heabs : |label a u-label A v-Real.pi/6| = 0 := by
    linarith [h.remainder_nonneg,abs_nonneg (label a u-label A v-Real.pi/6)]
  have he := abs_eq_zero.mp heabs
  have hid := remainder_identity a u
  have hslack := h.slack_nonneg
  have ha : a = 1 := by nlinarith [sq_nonneg (u-1/2)]
  have hu : u = 1/2 := by nlinarith [sq_nonneg (a-1)]
  have hv : v = 0 := by
    rw [hT,hA,ha,hu] at he
    dsimp [side,axial] at he
    linarith
  exact ⟨ha,hu,hv⟩

end SquaresInCircles.Seven
