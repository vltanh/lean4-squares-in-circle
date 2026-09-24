import SquaresInCircles.Seven.TargetProfiles
import SquaresInCircles.Seven.BoundarySegments
import SquaresInCircles.Seven.CapReduction

/-!
# The forward axis, negative target sign

A positive source with any active label, and a negative source with an axial
label. The side-target minimum at medium angles comes from the tangent of the
disk at the transition state.
-/
noncomputable section
namespace SquaresInCircles.Seven
open Boundary

private def rawTarget (A v e r : ℝ) : ℝ :=
  1/2+(4/5)*r-(A-1/2)*Real.cos e-v*Real.sin e+|Real.sin e|/2

lemma forward_negative_target_lower {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u) :
    rawTarget A v (sgn.coe*label a u+label A v-Real.pi/6)
      (sgn.coe*label a u) ≤ pairSupport a u A v sgn .negative 1 gap := by
  let e := sgn.coe*label a u+label A v-Real.pi/6
  have herange : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/2 := by
    have ht0 := h.label_nonneg
    have hs0 := h'.label_nonneg
    have ht1 := h.label_le_quarter
    have hs1 := h'.label_le_quarter
    cases sgn <;> dsimp [e,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  have hc : 0 ≤ Real.cos e := cos_nonneg_quarter herange
  have hsource' : (4/5)*(sgn.coe*label a u) ≤ sgn.coe*u := by
    rcases hsource with rfl | he
    · have hh := h.label_le_axial
      dsimp [TransverseSign.coe,axial] at *
      linarith
    · rw [he]
      dsimp [axial]
      cases sgn <;> norm_num [TransverseSign.coe]
  have hangle : 3*Real.pi/2-gap-sgn.coe*label a u-label A v=Real.pi-e := by
    dsimp [e,gap]
    ring
  rw [pairSupport_one,show TransverseSign.negative.coe = -1 from rfl]
  simp only [neg_one_mul,← sub_eq_add_neg]
  rw [hangle]
  simp only [support,Real.cos_pi_sub,Real.sin_pi_sub,abs_neg,abs_of_nonneg hc]
  change rawTarget A v e (sgn.coe*label a u) ≤ _
  dsimp [rawTarget]
  linarith

lemma side_transition_trade {A v : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) :
    (12/25)*(v-u0) ≤ a0-A := by
  have hb := side_state_transition_bounds h hT
  have he := transition_circle
  have hc := transition_bounds
  have hp := h.2.2.2
  have ht : X0*(A-a0)+Y0*(v-u0) ≤ 0 := by
    dsimp [phi,a0,u0] at hp ⊢
    nlinarith [sq_nonneg (A+1/2-X0),sq_nonneg (v+1/2-Y0)]
  have hratio : (12/25)*X0 < Y0 := by
    dsimp [a0,u0] at hc
    linarith
  have hm := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hratio.le)
  have hXpos : 0 < X0 := by dsimp [a0] at hc; linarith
  by_contra hn
  have hbad := mul_pos
    (show 0 < (12/25)*(v-u0)-(a0-A) by linarith) hXpos
  nlinarith

def sideTarget (A v e : ℝ) : ℝ :=
  (4/5)*e+(2/15)*remainder A v+(A-1/2)*(1-Real.cos e)
    -v*Real.sin e+|Real.sin e|/2

lemma sideTarget_positive_angle {A v e : ℝ} (h : Admissible A v)
    (he : 0 ≤ e ∧ e ≤ Real.pi/3) :
    (21/40)*e+(2/15)*remainder A v ≤ sideTarget A v e := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he.1
    (by linarith [he.2,Real.pi_pos])
  have hs1 := Real.sin_le he.1
  have hc := mul_nonneg (show 0 ≤ A-1/2 by linarith [h.2.2.1])
    (sub_nonneg.mpr (Real.cos_le_one e))
  have hv := mul_nonneg (show 0 ≤ 31/40-v by linarith [h.u_lt]) hs0
  have hrem := mul_nonneg (show (0:ℝ) ≤ 11/40 by norm_num) (sub_nonneg.mpr hs1)
  dsimp [sideTarget]
  rw [abs_of_nonneg hs0]
  nlinarith

lemma sideTarget_short_negative {A v z : ℝ} (h : Admissible A v)
    (hz : 0 < z ∧ z ≤ 1/6) : 0 < sideTarget A v (-z) := by
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower_157])
  have hdot := dot_lower_candidate (p := 3/5-Real.cos z)
    (r := Real.sin z-4/15) h.2.2.2
  have hid : sideTarget A v (-z) = shortTargetL z+
      (3/5-Real.cos z)*(A+1/2)+(Real.sin z-4/15)*(v+1/2) := by
    dsimp [sideTarget,shortTargetL,remainder]
    rw [Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hs0]
    ring
  have hrad : (3/5-Real.cos z)^2+(Real.sin z-4/15)^2=shortTargetRad z := by
    dsimp [shortTargetRad]; ring
  rw [hrad] at hdot
  rw [hid]
  linarith [short_target_profile hz]

lemma sideTarget_transition_negative {z : ℝ} (hz : 1/6 ≤ z ∧ z ≤ 1) :
    0 < sideTarget a0 u0 (-z) := by
  have hc := transition_coarse
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0 ≤ z)
    (by linarith [hz.2,pi_lower_157])
  have hsin := Real.sin_ge_sub_cube (show 0 ≤ z by linarith)
  have hcos := cos_upper_four (show 0 ≤ z by linarith)
  have hsinU := Real.sin_le (show 0 ≤ z by linarith)
  have hcomp0 := sub_nonneg.mpr (Real.cos_le_one z)
  have hpA := mul_nonneg (show 0 ≤ a0-1/2-3/5 by linarith) hcomp0
  have hpU := mul_nonneg (show 0 ≤ u0+1/2-79/100 by linarith) hs0
  have hcube := mul_nonneg (pow_nonneg (show 0 ≤ z by linarith) 3)
    (show (0:ℝ) ≤ 4/5-79/100 by norm_num)
  have hz3 : z^3 ≤ z^2 := by
    have hh := mul_nonneg (sq_nonneg z) (show 0 ≤ 1-z by linarith)
    nlinarith
  have hz4 : z^4 ≤ z^2 := by
    have hsq : z^2 ≤ 1 := by nlinarith
    have hh := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hsq)
    nlinarith
  have hprof : -z/100+(17/120)*z^2 ≤ sideTarget a0 u0 (-z) := by
    have hW := transition_admissible.remainder_nonneg
    dsimp [sideTarget]
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs0]
    nlinarith
  have hpos := mul_pos (show 0 < z by linarith)
    (show 0 < -1/100+(17/120)*z by linarith [hz.1])
  nlinarith

lemma sideTarget_negative_pos {A v z : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (hz : 0 < z ∧ z < 1) :
    0 < sideTarget A v (-z) := by
  by_cases hsmall : z ≤ 1/6
  · exact sideTarget_short_negative h ⟨hz.1,hsmall⟩
  have hbig : 1/6 ≤ z := (lt_of_not_ge hsmall).le
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower_157])
  have hc0 : (1:ℝ)/2 < Real.cos z := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := z)
    nlinarith
  have hb := side_state_transition_bounds h hT
  have ht := side_transition_trade h hT
  have hc := transition_coarse
  have hexp (a u : ℝ) : sideTarget a u (-z) =
      Real.cos z/2+Real.sin z/2+1/30-(4/5)*z+
      (3/5-Real.cos z)*a+(Real.sin z-4/15)*u := by
    dsimp [sideTarget,remainder]
    rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs0]
    ring
  by_cases hcos : 3/5 ≤ Real.cos z
  · have hcompare : sideTarget a0 u0 (-z) ≤ sideTarget A v (-z) := by
      rw [hexp,hexp]
      by_cases hsin : 4/15 ≤ Real.sin z
      · have h1 := mul_nonneg (show 0 ≤ Real.cos z-3/5 by linarith)
          (show 0 ≤ a0-A by linarith [hb.2.1])
        have h2 := mul_nonneg (show 0 ≤ Real.sin z-4/15 by linarith)
          (show 0 ≤ v-u0 by linarith [hb.1])
        nlinarith
      · have hcos' : 24/25 < Real.cos z := by
          nlinarith [Real.sin_sq_add_cos_sq z]
        have hsin' : (33:ℝ)/200 < Real.sin z := by
          have hm := sin_le_sin_half
            (x := 1/6) (y := z)
            (by constructor <;> linarith [pi_lower_157])
            (by constructor <;> linarith [hz.1,hz.2,pi_lower_157]) hbig
          have hl := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 1/6 by norm_num)
          linarith
        have h1 := mul_nonneg (show 0 ≤ Real.cos z-3/5 by linarith)
          (show 0 ≤ a0-A-(12/25)*(v-u0) by linarith)
        have h2 := mul_nonneg (show 0 ≤ v-u0 by linarith [hb.1])
          (show 0 ≤ (12/25)*(Real.cos z-3/5)+Real.sin z-4/15 by linarith)
        nlinarith
    exact (sideTarget_transition_negative ⟨hbig,hz.2.le⟩).trans_le hcompare
  · have hsin : 4/5 < Real.sin z := by
      nlinarith [Real.sin_sq_add_cos_sq z]
    have h1 := mul_nonneg (show 0 ≤ 3/5-Real.cos z by linarith) h.a_nonneg
    have h2 := mul_nonneg (show 0 ≤ v-29/100 by linarith [hb.1,hc.2.2.1])
      (show 0 ≤ Real.sin z-4/15 by linarith)
    rw [hexp]
    nlinarith

lemma negative_target_axial_pos {A v e r : ℝ}
    (h : Admissible A v) (hA : label A v=axial v)
    (he : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3)
    (hr : e=r+label A v-Real.pi/6) : 0 < rawTarget A v e r := by
  have hv : v ≤ Real.pi/5 := by
    have hh := h.label_le_quarter
    rw [hA] at hh
    dsimp [axial] at hh
    linarith
  have hidentity : rawTarget A v e r =
      1/2+2*Real.pi/15+(4/5)*e-(A-1/2)*Real.cos e-
      v*(1+Real.sin e)+|Real.sin e|/2 := by
    rw [hA] at hr
    dsimp [rawTarget,axial] at *
    linarith
  rw [hidentity]
  by_cases he0 : 0 ≤ e
  · have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi he0
      (by linarith [he.2,Real.pi_pos])
    have hsin := Real.sin_le he0
    have hc := mul_nonneg (show 0 ≤ A-1/2 by linarith [h.2.2.1])
      (sub_nonneg.mpr (Real.cos_le_one e))
    have hp := mul_nonneg (show 0 ≤ 13/20-v by linarith [pi_lt_22_over_7]) hs0
    have hm := mul_nonneg (show (0:ℝ) ≤ 3/20 by norm_num) (sub_nonneg.mpr hsin)
    rw [abs_of_nonneg hs0]
    have hsum := axial_sum_lt h hA
    nlinarith [pi_lower_157]
  · let z := -e
    have hz : 0 ≤ z ∧ z ≤ Real.pi/2 := by dsimp [z]; constructor <;> linarith [he.1]
    have hez : e = -z := by dsimp [z]; ring
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1 (by linarith [hz.2,Real.pi_pos])
    rw [hez,Real.cos_neg,Real.sin_neg,abs_neg,abs_of_nonneg hs0]
    by_cases hs : z ≤ 1/3
    · have hp := axial_target_small_support h hA ⟨hz.1,hs⟩
      nlinarith
    · have hp := axial_target_large_support h ⟨(lt_of_not_ge hs).le,hz.2⟩
      nlinarith

lemma negative_target_side_nonneg {A v e r : ℝ}
    (h : Admissible A v) (hT : label A v=side A v)
    (he : -1 < e ∧ e ≤ Real.pi/3)
    (hr : e=r+label A v-Real.pi/6) : 0 ≤ rawTarget A v e r := by
  have hid : rawTarget A v e r=sideTarget A v e := by
    rw [hT,side_identity_radial] at hr
    dsimp [rawTarget,sideTarget]
    nlinarith
  rw [hid]
  by_cases he0 : 0 ≤ e
  · have hp := sideTarget_positive_angle h ⟨he0,he.2⟩
    linarith [h.remainder_nonneg]
  · have hp := sideTarget_negative_pos h hT
      (z := -e) ⟨by linarith,by linarith [he.1]⟩
    simpa using hp.le

lemma negative_target_side_pos {A v e r : ℝ}
    (h : StrictlyAdmissible A v) (hT : label A v=side A v)
    (he : -1 < e ∧ e ≤ Real.pi/3)
    (hr : e=r+label A v-Real.pi/6) : 0 < rawTarget A v e r := by
  have hid : rawTarget A v e r=sideTarget A v e := by
    rw [hT,side_identity_radial] at hr
    dsimp [rawTarget,sideTarget]
    nlinarith
  rw [hid]
  by_cases he0 : 0 ≤ e
  · have hp := sideTarget_positive_angle h.admissible ⟨he0,he.2⟩
    linarith [h.remainder_pos]
  · have hp := sideTarget_negative_pos h.admissible hT
      (z := -e) ⟨by linarith,by linarith [he.1]⟩
    simpa using hp

theorem fixed_gap_forward_negative_target {a u A v : ℝ} (sgn : TransverseSign)
    (h : Admissible a u) (h' : Admissible A v)
    (hsource : sgn=.positive ∨ label a u=axial u)
    (htarget : ActiveLabel A v) : PairProperty a u A v sgn .negative 1 := by
  let r := sgn.coe*label a u
  let e := r+label A v-Real.pi/6
  have hlow := forward_negative_target_lower sgn h h' hsource
  change rawTarget A v e r ≤ _ at hlow
  have he : -Real.pi/2 ≤ e ∧ e ≤ Real.pi/3 := by
    have h0 := h.label_nonneg
    have h1 := h.label_le_quarter
    have h2 := h'.label_nonneg
    have h3 := h'.label_le_quarter
    cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> constructor <;> linarith [Real.pi_pos]
  rcases htarget with hA | hT
  · have hp := negative_target_axial_pos h' hA he rfl
    exact ⟨hp.le.trans hlow,fun _ _ => hp.trans_le hlow⟩
  · have he' : -1 < e ∧ e ≤ Real.pi/3 := by
      have hs := side_selected_label_gt h' hT
      have h0 := h.label_nonneg
      have h1 := h.label_le_quarter
      constructor
      · cases sgn <;> dsimp [e,r,TransverseSign.coe] <;> linarith [pi_lt_22_over_7]
      · exact he.2
    refine ⟨(negative_target_side_nonneg h' hT he' rfl).trans hlow,?_⟩
    intro ha hb
    exact (negative_target_side_pos hb hT he' rfl).trans_le hlow

end SquaresInCircles.Seven
