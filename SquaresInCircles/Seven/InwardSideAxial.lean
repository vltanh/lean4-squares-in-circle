import SquaresInCircles.Seven.InwardTurnBounds
import SquaresInCircles.Seven.CapReduction
import SquaresInCircles.Seven.PairModel

/-!
# The inward axis, positive signs, side and axial labels

A lower bound through the relative turn. Equality forces the side state
`(1, 1/2)` and `v = 0` but leaves the axial coordinate `A` free, as in the
sliding packings.
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
  linarith [pi_lt_22_over_7]

/-- A lower bound through the remainder of the side state and the relative
turn. -/
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

/-- The inward axis with positive signs, side source and axial target. Zero
support forces the side state and zero transverse coordinate of the axial
square; no particular value of `A` is concluded. -/
theorem inward_side_axial_property {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u = side a u) (hA : label A v = axial v) :
    PairProperty a u A v .positive .positive 2 := by
  have hl := inward_side_axial_lower h h' hT hA
  have hW := h.remainder_nonneg
  have he := abs_nonneg (label a u-label A v-Real.pi/6)
  refine ⟨by linarith,fun hz => ?_⟩
  have hc := Equality.remainder_zero h (by linarith)
  have he0 : label a u-label A v-Real.pi/6 = 0 := abs_eq_zero.mp (by linarith)
  rw [hc.1,hc.2,Equality.side_label,hA] at he0
  dsimp [axial] at he0
  exact Or.inr (Or.inl ⟨rfl,hc,Equality.axial_of_transverse_zero h' (by linarith)⟩)

end SquaresInCircles.Seven
