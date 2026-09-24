import SquaresInCircles.Seven.PairModel
import SquaresInCircles.Seven.MarkerArc

/-!
# Whole-domain fixed-gap support sectors

The marker arc, not an unproved angular shadow statement, supplies the support
bound used for the inward-radial negative-sign sector.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma marker_arc_signed {a b x : ℝ} (h : Admissible a |b|)
    (hx : |x-signedLabel a b| ≤ 801/1600) :
    |Real.cos x-a| ≤ 1/2 ∧ |Real.sin x-b| ≤ 1/2 := by
  by_cases hb : b < 0
  · have ht : |-x-label a |b|| ≤ 801/1600 := by
      have he : -x-label a |b| = -(x-(-label a |b|)) := by ring
      rw [he,abs_neg]
      simpa only [signedLabel,if_pos hb] using hx
    have hm := marker_arc h ht
    rw [Real.cos_neg,Real.sin_neg] at hm
    refine ⟨hm.1,?_⟩
    have he : -Real.sin x-|b| = -(Real.sin x-b) := by rw [abs_of_neg hb]; ring
    rw [he,abs_neg] at hm
    exact hm.2
  · simpa only [signedLabel,if_neg hb,abs_of_nonneg (le_of_not_gt hb)] using
      marker_arc h (by simpa only [signedLabel,if_neg hb] using hx)

lemma marker_arc_support {a b x : ℝ} (h : Admissible a |b|)
    (hx : |x-signedLabel a b| ≤ 801/1600) (z : ℝ) :
    Real.cos (z-x) ≤ support a b z := by
  have hm := marker_arc_signed h hx
  have hs := point_le_support hm.1 hm.2 z
  simpa only [Real.cos_sub,mul_comm] using hs

/-- Outward radial source: no active-label case distinction. -/
theorem fixed_gap_outward {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (s t : TransverseSign) :
    0 < pairSupport a u A v s t 0 gap := by
  rw [pairSupport_zero]
  exact outward_support_pos h.2.2.1 (sign_admissible h' t) _

/-- Backward transverse source: the other square's marker point suffices. -/
theorem fixed_gap_backward {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (s t : TransverseSign) :
    0 < pairSupport a u A v s t 3 gap := by
  rw [pairSupport_three]
  have hp := marker_support_lower (sign_admissible h' t)
    (5*Real.pi/2-gap-s.coe*label a u+t.coe*label A v)
  rw [sign_label h' t] at hp
  have he : 5*Real.pi/2-gap-s.coe*label a u+t.coe*label A v-t.coe*label A v =
      5*Real.pi/2-(gap+s.coe*label a u) := by ring
  rw [he,cos_five_half_pi_sub] at hp
  have h0 := h.label_nonneg
  have h1 := h.label_le_quarter
  cases s
  · have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.pi/6-label a u)
    have hid : Real.sin (gap+label a u) = Real.cos (Real.pi/6-label a u) := by
      have he : gap+label a u = Real.pi/2-(Real.pi/6-label a u) := by dsimp [gap]; ring
      rw [he,Real.sin_pi_div_two_sub]
    have hr : -(3/5 : ℝ) < Real.pi/6-label a u ∧
        Real.pi/6-label a u < 3/5 := by
      constructor <;> linarith [Real.pi_lt_d4,Real.pi_pos]
    have hsq : (Real.pi/6-label a u)^2 < (3/5 : ℝ)^2 := by nlinarith [hr.1,hr.2]
    simp only [TransverseSign.coe,one_mul] at hp ⊢
    rw [hid] at hp
    linarith [h.u_lt]
  · have hs : 0 ≤ Real.sin (gap-label a u) :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        (by dsimp [gap]; linarith [Real.pi_pos])
        (by dsimp [gap]; linarith [Real.pi_pos])
    simp only [TransverseSign.coe,neg_one_mul,sub_neg_eq_add] at hp ⊢
    have he : gap+-label a u = gap-label a u := by ring
    rw [he] at hp
    linarith [h.1]

/-- The inward radial source is uniformly positive when its transverse sign
is negative. The other square may have either sign and any active label. -/
theorem fixed_gap_inward_negative {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) (t : TransverseSign) :
    0 < pairSupport a u A v .negative t 2 gap := by
  rw [pairSupport_two]
  simp only [TransverseSign.coe,neg_one_mul,sub_neg_eq_add]
  let x := t.coe*label A v-801/1600
  let z := 2*Real.pi-gap+label a u+t.coe*label A v
  have hx : |x-signedLabel A (t.coe*v)| ≤ 801/1600 := by
    rw [sign_label h' t]
    dsimp [x]
    norm_num
  have hp := marker_arc_support (sign_admissible h' t) hx z
  have he : z-x = 2*Real.pi- (gap-label a u-801/1600) := by dsimp [z,x]; ring
  rw [he,cos_two_pi_sub] at hp
  have hb : -(2/3 : ℝ) < gap-label a u-801/1600 ∧
      gap-label a u-801/1600 < 2/3 := by
    have h0 := h.label_nonneg
    have h1 := h.label_le_quarter
    dsimp [gap]
    constructor <;> linarith [Real.pi_gt_d2,Real.pi_lt_d4]
  have hc := Real.one_sub_sq_div_two_le_cos (x := gap-label a u-801/1600)
  have hsq : (gap-label a u-801/1600)^2 < (2/3 : ℝ)^2 := by nlinarith [hb.1,hb.2]
  have ha := h.a_le_sqrt_three
  have hr : Real.sqrt 3 < 7/4 := by
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  change 0 < 1/2-a+support A (t.coe*v) z
  linarith

end SquaresInCircles.Seven
