import SquaresInCircles.Seven.EasySectors
import SquaresInCircles.Seven.SectorBounds

/-!
# Forward transverse support, both transverse signs positive

This closes this whole source/sign sector without selecting an active label.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma support_pi_shift (a b z : ℝ) :
    support a b (Real.pi+z) =
      -a*Real.cos z-b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2 := by
  simp [support,Real.cos_add,Real.sin_add,abs_neg]
  ring

lemma support_three_half_sub (a b z : ℝ) :
    support a b (3*Real.pi/2-z) =
      -a*Real.sin z-b*Real.cos z+(|Real.sin z|+|Real.cos z|)/2 := by
  rw [show 3*Real.pi/2-z = Real.pi+(Real.pi/2-z) by ring]
  rw [support_pi_shift,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]

lemma support_two_pi_sub (a b z : ℝ) :
    support a b (2*Real.pi-z) =
      a*Real.cos z-b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2 := by
  simp [support,Real.cos_sub,Real.sin_sub,Real.cos_two_mul,Real.sin_two_mul,abs_neg]
  ring

/-- Closed containment suffices for strict positivity in this entire sector. -/
theorem fixed_gap_forward_positive {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    0 < pairSupport a u A v .positive .positive 1 gap := by
  let t := label a u
  let s := label A v
  let z := Real.pi/6-t+s
  have ht0 : 0 ≤ t := h.label_nonneg
  have ht1 : t ≤ Real.pi/4 := h.label_le_quarter
  have hs0 : 0 ≤ s := h'.label_nonneg
  have hs1 : s ≤ Real.pi/4 := h'.label_le_quarter
  have htu : (4/5)*t ≤ u := by
    have hh := h.label_le_axial
    dsimp [axial] at hh
    dsimp [t]
    linarith
  have he : pairSupport a u A v .positive .positive 1 gap =
      1/2+u+support A v (Real.pi+z) := by
    rw [pairSupport_one]
    simp only [TransverseSign.coe,one_mul]
    congr 2
    dsimp [gap,z,t,s]
    ring
  rw [he]
  by_cases ht : 5/16 ≤ t
  · have hl := support_lower
      (by simpa only [abs_of_nonneg h'.1] using h') (Real.pi+z)
    linarith [htu,sqrt_three_bounds.2]
  · have ht' : 0 ≤ t ∧ t ≤ 5/16 := ⟨ht0,(lt_of_not_ge ht).le⟩
    have hz : 0 ≤ z ∧ z ≤ Real.pi/2 := by
      dsimp [z]
      constructor <;> linarith [pi_lower_157,Real.pi_pos]
    have hc : 0 ≤ Real.cos z := cos_nonneg_quarter
      ⟨by linarith [hz.1,Real.pi_pos],hz.2⟩
    have hsn : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    rw [support_pi_shift,abs_of_nonneg hc,abs_of_nonneg hsn]
    by_cases hquarter : Real.pi/4 ≤ z
    · have hcs := cos_le_sin_of_quarter ⟨hquarter,hz.2⟩
      have hp := mul_nonneg (show 0 ≤ A-v by linarith [h'.2.1])
        (show 0 ≤ Real.sin z-Real.cos z by linarith)
      have hsum := h'.sum_lt
      have hnon := add_nonneg hc hsn
      have hprod := mul_nonneg (show 0 ≤ 31/20-A-v by linarith) hnon
      have hunit := sin_add_cos_le_three_halves z
      nlinarith [h.1]
    · have hquarter' : z ≤ Real.pi/4 := (lt_of_not_ge hquarter).le
      have hd := dot_upper_unit h'.2.2.2
        (C := Real.cos z) (S := Real.sin z)
        (by nlinarith [Real.sin_sq_add_cos_sq z])
      have hw : 0 ≤ Real.pi/6-t ∧ Real.pi/6-t ≤ Real.pi/4 := by
        constructor <;> linarith [pi_lower_157,Real.pi_pos]
      have hm := trig_sum_monotone hw ⟨hz.1,hquarter'⟩
        (show Real.pi/6-t ≤ z by dsimp [z]; linarith)
      have hf := forward_positive_profile ht'
      dsimp [phi] at hd
      nlinarith

end SquaresInCircles.Seven
