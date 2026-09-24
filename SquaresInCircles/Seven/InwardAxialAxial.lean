import SquaresInCircles.Seven.InwardSideAxial
import SquaresInCircles.Seven.AxialProfile

/-!
# The inward axis, positive signs, two axial labels

The axial sum bound and the axial profile give strict positivity, even for
closed containment and for both signs of the relative turn.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma axial_remainder_pos {a u : ℝ} (h : Admissible a u)
    (hA : label a u = axial u) : 0 < remainder a u := by
  have hw := h.remainder_nonneg
  by_contra hn
  have hzero : remainder a u = 0 := by linarith
  have hid := remainder_identity a u
  have hslack := h.slack_nonneg
  have ha : a = 1 := by nlinarith [sq_nonneg (u-1/2)]
  have hu : u = 1/2 := by nlinarith [sq_nonneg (a-1)]
  have hle := h.label_le_side
  rw [hA,ha,hu] at hle
  dsimp [axial,side] at hle
  linarith [pi_lt_22_over_7]

lemma inward_positive_signs_formula {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .positive .positive 2 gap =
      1-a-v-A*Real.sin (label a u-label A v-Real.pi/6)+
      |Real.sin (label a u-label A v-Real.pi/6)|/2+
      (v-1/2)*(1-Real.cos (label a u-label A v-Real.pi/6)) := by
  let e := label a u-label A v-Real.pi/6
  have he : -5*Real.pi/12 ≤ e ∧ e ≤ Real.pi/12 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [e]
    constructor <;> linarith
  have hc : 0 ≤ Real.cos e := cos_nonneg_quarter
    ⟨by linarith [he.1,Real.pi_pos],by linarith [he.2,Real.pi_pos]⟩
  have hangle : 2*Real.pi-gap-label a u+label A v = 3*Real.pi/2-e := by
    dsimp [gap,e]
    ring
  have hcos : Real.cos (3*Real.pi/2-e) = -Real.sin e := by
    rw [show 3*Real.pi/2-e = (Real.pi+Real.pi/2)-e by ring]
    simp [Real.cos_sub,Real.cos_add,Real.sin_add]
  have hsin : Real.sin (3*Real.pi/2-e) = -Real.cos e := by
    rw [show 3*Real.pi/2-e = (Real.pi+Real.pi/2)-e by ring]
    simp [Real.sin_sub,Real.cos_add,Real.sin_add]
  rw [pairSupport_two]
  simp only [TransverseSign.coe,one_mul]
  rw [hangle]
  change _ = 1-a-v-A*Real.sin e+|Real.sin e|/2+(v-1/2)*(1-Real.cos e)
  simp only [support,hcos,hsin,abs_neg,abs_of_nonneg hc]
  ring

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

/-- Global strict positivity for the inward-radial (+,+), axial/axial sector. -/
theorem inward_axial_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u = axial u) (hB : label A v = axial v) :
    0 < pairSupport a u A v .positive .positive 2 gap := by
  let e := label a u-label A v-Real.pi/6
  have he : -5*Real.pi/12 ≤ e ∧ e ≤ Real.pi/12 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [e]
    constructor <;> linarith
  rw [inward_positive_signs_formula h h']
  change 0 < 1-a-v-A*Real.sin e+|Real.sin e|/2+(v-1/2)*(1-Real.cos e)
  by_cases he0 : 0 ≤ e
  · have hclear := inward_axial_target_clearance h hB
    change (4/5)*e+(2/15)*remainder a u ≤ 1-a-v at hclear
    have hturn := inward_positive_turn_bound h'.a_le_sqrt_three h'.1 ⟨he0,he.2⟩
    have hw := axial_remainder_pos h hA
    linarith
  · let z := -e
    have hz : 0 ≤ z ∧ z ≤ Real.pi/2 := by
      dsimp [z]
      constructor <;> linarith [he.1,Real.pi_pos]
    have hez : e = -z := by dsimp [z]; ring
    have hs0 : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi
      hz.1 (by linarith [hz.2,Real.pi_pos])
    have hc0 : 0 ≤ Real.cos z := cos_nonneg_quarter
      ⟨by linarith [hz.1,Real.pi_pos],hz.2⟩
    have hd0 : 0 ≤ 1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
    have hAprod := mul_nonneg (show 0 ≤ A-1/2 by linarith [h'.2.2.1]) hs0
    have hv : v = u+(4/5)*z-2*Real.pi/15 := by
      dsimp [e] at hez
      rw [hA,hB] at hez
      dsimp [axial] at hez
      linarith
    let b0 : ℝ := 1/2+2*Real.pi/15
    have hid :
        1-a-v+(A+1/2)*Real.sin z+(v-1/2)*(1-Real.cos z) =
        1+2*Real.pi/15-a-u+
          (Real.sin z-(4/5)*z*Real.cos z-(b0-u)*(1-Real.cos z))+
          (A-1/2)*Real.sin z := by
      rw [hv]
      dsimp [b0]
      ring
    rw [hez,Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs0]
    have htgt :
        0 < 1-a-v+(A+1/2)*Real.sin z+(v-1/2)*(1-Real.cos z) := by
      rw [hid]
      by_cases hu : 1/20 ≤ u
      · have hb : b0-u ≤ 7/8 := by dsimp [b0]; linarith [pi_lt_22_over_7]
        have hp := axial_profile_parameter_nonneg hb hz
        have hsum := axial_sum_lt h hA
        linarith [pi_lower_157]
      · have hu' : u < 1/20 := lt_of_not_ge hu
        have hsum : a+u < 77/60 := by
          linarith [h.a_le_sqrt_three,sqrt_three_bounds.2]
        have hb : 0 ≤ b0-7/8 ∧ b0-7/8 < 1/20 := by
          dsimp [b0]
          constructor <;> linarith [pi_lower_157,pi_lt_22_over_7]
        have hprod := mul_le_mul_of_nonneg_left
          (show 1-Real.cos z ≤ 1 by linarith) hb.1
        have hupos := mul_nonneg h.1 hd0
        have hp := axial_profile_nonneg hz
        dsimp [axialProfile] at hp
        nlinarith [pi_lower_157]
    nlinarith

end SquaresInCircles.Seven
