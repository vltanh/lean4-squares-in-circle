import SquaresInCircles.Seven.InwardTurnBounds
import SquaresInCircles.Seven.AxialProfile
import SquaresInCircles.Seven.Contacts

/-!
# The inward axis, positive signs, two axial labels

The axial sum bound and the axial profile give strict positivity, even for
closed containment and for both signs of the relative turn. The nonpositive
turn is treated for either target sign.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma axial_remainder_pos {a u : ℝ} (h : Admissible a u)
    (hA : label a u = axial u) : 0 < remainder a u := by
  refine h.remainder_nonneg.lt_of_ne fun hz => ?_
  have hc := Equality.remainder_zero h hz.symm
  have hle := h.label_le_side
  rw [hA,hc.1,hc.2] at hle
  dsimp [axial,side] at hle
  linarith [pi_lt_22_over_7]

/-- The signed radial label inequality retains the source containment remainder
without requiring the source label to be side-selected. -/
lemma inward_axial_target_clearance {a u A v : ℝ}
    (h : Admissible a u) (hA : label A v = axial v) :
    (4/5)*(label a u-label A v-Real.pi/6)+(2/15)*remainder a u ≤ 1-a-v := by
  have ht := h.label_le_side
  rw [side_identity_radial] at ht
  rw [hA]
  dsimp [axial]
  linarith

/-- Two axial labels and a nonpositive turn, for either target sign: the axial
profile bounds the sum below. -/
lemma inward_axial_nonpositive_turn {a u A v : ℝ} (t : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u = axial u) (hB : label A v = axial v)
    (he : label a u-t.coe*label A v-Real.pi/6 ≤ 0) :
    0 < pairSupport a u A v .positive t 2 gap := by
  let z := -(label a u-t.coe*label A v-Real.pi/6)
  have hz : 0 ≤ z ∧ z ≤ Real.pi/2 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h'.label_le_quarter
    dsimp [z]
    cases t <;> simp only [TransverseSign.coe] at he ⊢ <;> constructor <;> linarith
  have hb : t.coe*v = u+(4/5)*z-2*Real.pi/15 := by
    dsimp [z]
    rw [hA,hB]
    dsimp [axial]
    ring
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [Real.pi_pos])
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hz.2⟩
  have hp := axial_profile_nonneg hz
  have hsum := axial_sum_lt h hA
  have h0 := mul_nonneg hc (show 0 ≤ 1+2*Real.pi/15-a-u-1/200 by linarith [pi_lower_157])
  have h1 := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z))
    (show 0 ≤ 11/8-a-1/200 by linarith [h.a_le_sqrt_three_sub_half,sqrt_three_bounds.2])
  have h2 := mul_nonneg (show 0 ≤ A-1/2 by linarith [h'.2.2.1]) hs
  rw [pairSupport_inward t h h',show label a u-t.coe*label A v-Real.pi/6 = -z by dsimp [z]; ring,
    Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs,hb]
  dsimp [axialProfile] at hp
  linarith

/-- Global strict positivity for the inward-radial (+,+), axial/axial sector. -/
theorem inward_axial_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u = axial u) (hB : label A v = axial v) :
    0 < pairSupport a u A v .positive .positive 2 gap := by
  let e := label a u-label A v-Real.pi/6
  by_cases he0 : e ≤ 0
  · exact inward_axial_nonpositive_turn .positive h h' hA hB
      (by simp only [TransverseSign.coe,one_mul]; exact he0)
  have hclear := inward_axial_target_clearance h hB
  change (4/5)*e+(2/15)*remainder a u ≤ 1-a-v at hclear
  have hturn := inward_positive_turn_bound h'.a_le_sqrt_three_sub_half h'.1
    ⟨(lt_of_not_ge he0).le,by dsimp [e]; linarith [h.label_le_quarter,h'.label_nonneg]⟩
  have hw := axial_remainder_pos h hA
  rw [pairSupport_inward .positive h h']
  simp only [TransverseSign.coe,one_mul]
  change 0 < 1/2-a-A*Real.sin e+|Real.sin e|/2+(1/2-v)*Real.cos e
  linarith

end SquaresInCircles.Seven
