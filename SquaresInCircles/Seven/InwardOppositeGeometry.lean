import SquaresInCircles.Seven.BoundarySegments
import SquaresInCircles.Seven.InwardAxialAxial

/-!
# The inward axis with opposite signs: formula and displacements

The exact support formula, and displacement bounds along the two pieces of the
axial boundary and the circular side boundary, which avoid differentiating the
minimum at its corner.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

def inwardOpposite (a A v e : ℝ) : ℝ :=
  1/2-a-A*Real.sin e+|Real.sin e|/2+(v+1/2)*Real.cos e

lemma inward_opposite_formula {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .positive .negative 2 gap =
      inwardOpposite a A v (label a u+label A v-Real.pi/6) := by
  let e := label a u+label A v-Real.pi/6
  have hr : -Real.pi/6 ≤ e ∧ e ≤ Real.pi/3 := by
    have ht0 := h.label_nonneg
    have hs0 := h'.label_nonneg
    have ht1 := h.label_le_quarter
    have hs1 := h'.label_le_quarter
    dsimp [e]
    constructor <;> linarith
  have hc : 0 ≤ Real.cos e := cos_nonneg_quarter
    ⟨by linarith [hr.1,Real.pi_pos],by linarith [hr.2,Real.pi_pos]⟩
  have he : 2*Real.pi-gap-label a u+-label A v=3*Real.pi/2-e := by
    dsimp [e,gap]; ring
  rw [pairSupport_two]
  simp only [TransverseSign.coe,one_mul,neg_one_mul]
  rw [he]
  have hcos : Real.cos (3*Real.pi/2-e) = -Real.sin e := by
    rw [show 3*Real.pi/2-e=Real.pi+(Real.pi/2-e) by ring]
    simp [Real.cos_add,Real.cos_pi_div_two_sub]
  have hsin : Real.sin (3*Real.pi/2-e) = -Real.cos e := by
    rw [show 3*Real.pi/2-e=Real.pi+(Real.pi/2-e) by ring]
    simp [Real.sin_add,Real.sin_pi_div_two_sub]
  simp only [support,hcos,hsin,abs_neg,abs_of_nonneg hc,inwardOpposite]
  ring

lemma inward_opposite_side_identity {a u A v e : ℝ}
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : e=label a u+label A v-Real.pi/6) :
    inwardOpposite a A v e =
      (4/5)*e+(2/15)*remainder a u-A*Real.sin e+|Real.sin e|/2-
        (v+1/2)*(1-Real.cos e) := by
  rw [hT,hA] at he
  dsimp [inwardOpposite,side,axial,remainder] at *
  nlinarith

lemma inward_opposite_negative_turn {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : label a u+label A v-Real.pi/6 ≤ 0) :
    (2/15)*remainder a u+|label a u+label A v-Real.pi/6|/12 ≤
      pairSupport a u A v .positive .negative 2 gap := by
  let z := -(label a u+label A v-Real.pi/6)
  have hz : 0 ≤ z ∧ z ≤ 1/6 := by
    have ht := side_selected_label_gt h hT
    have hs := h'.label_nonneg
    dsimp [z]
    constructor <;> linarith [pi_lt_22_over_7]
  have hv : v+1/2 < 6/5 := by
    have hs := h'.label_le_quarter
    rw [hA] at hs
    dsimp [axial] at hs
    linarith [pi_lt_22_over_7]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,pi_lower_157])
  have hs := Real.sin_ge_sub_cube hz.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have hpA := mul_nonneg (show 0 ≤ A-1/2 by linarith [h'.2.2.1]) hs0
  have hpV := mul_nonneg (show 0 ≤ 6/5-(v+1/2) by linarith)
    (sub_nonneg.mpr (Real.cos_le_one z))
  have hfactor : 1/12 ≤ 1/5-(3/5)*z-z^2/6 := by nlinarith
  have hprod := mul_nonneg hz.1 (sub_nonneg.mpr hfactor)
  rw [inward_opposite_formula h h',inward_opposite_side_identity hT hA rfl]
  have hez : label a u+label A v-Real.pi/6 = -z := by dsimp [z]; ring
  rw [hez,Real.sin_neg,Real.cos_neg,abs_neg z,abs_neg (Real.sin z),abs_of_nonneg hs0,
    abs_of_nonneg hz.1]
  nlinarith

namespace Boundary

lemma axialTop_antitone {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.pi/5) :
    axialTop v ≤ axialTop u := by
  have hvr : v ≤ rd := by linarith [hv,pi_lt_22_over_7,rd_bounds.1]
  have hc := (circle_order hu huv hvr).1
  have hl : axialLine v ≤ axialLine u := by dsimp [axialLine]; linarith
  exact min_le_min hc hl

lemma axialTop_displacement {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ Real.pi/5) :
    axialTop u-axialTop v ≤ (11/9)*(v-u) := by
  have hvr : v ≤ rd := by linarith [hv,pi_lt_22_over_7,rd_bounds.1]
  have hc := (circle_order hu huv hvr).2
  by_cases hm : circle v ≤ axialLine v
  · have hv' : axialTop v=circle v := min_eq_left hm
    have hu' : axialTop u ≤ circle u := min_le_left _ _
    rw [hv']
    linarith
  · have hv' : axialTop v=axialLine v := min_eq_right (le_of_not_ge hm)
    have hu' : axialTop u ≤ axialLine u := min_le_right _ _
    rw [hv']
    dsimp [axialLine] at hu' ⊢
    linarith

lemma circle_displacement_half {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ u0) :
    circle u-circle v ≤ (1/2)*(v-u) := by
  have hur : v ≤ rd := by linarith [hv,transition_coarse.2.2.2.1,rd_bounds.1]
  have ho := circle_order hu huv hur
  have h0u := circle_order hu (huv.trans hv)
    (show u0 ≤ rd by linarith [transition_coarse.2.2.2.1,rd_bounds.1])
  have h0v := circle_order (hu.trans huv) hv
    (show u0 ≤ rd by linarith [transition_coarse.2.2.2.1,rd_bounds.1])
  rw [circle_u0] at h0u h0v
  have eu := circle_eq ⟨hu,huv.trans hur⟩
  have ev := circle_eq ⟨hu.trans huv,hur⟩
  have hbounds := transition_bounds
  have hratio : 2*(u+v+1) ≤ circle u+circle v+1 := by linarith
  have hid : (circle u-circle v)*(circle u+circle v+1) = (v-u)*(u+v+1) := by
    nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hratio)
  have hden : 0 < circle u+circle v+1 := by linarith [transition_coarse.1]
  by_contra hn
  have hh := mul_pos
    (show 0 < circle u-circle v-(1/2)*(v-u) by linarith) hden
  nlinarith

lemma sideA_displacement {t s : ℝ}
    (ht : s0 ≤ t) (hts : t ≤ s) (hs : s ≤ td) :
    sideA t-sideA s ≤ (12/13)*(s-t) := by
  let f : ℝ → ℝ := fun x => sideA x+(12/13)*x
  have hm : MonotoneOn f (Icc t s) := by
    apply monoOn_of_hasDeriv_nonneg (d := fun x => 12/13-Y x/Z x)
      (fun x hx => by
        have hh := (hasDerivAt_X ⟨ht.trans hx.1,hx.2.trans hs⟩).sub_const (1/2)
        exact (hh.add ((hasDerivAt_id x).const_mul (12/13))).continuousAt.continuousWithinAt)
    · intro x hx
      exact (((hasDerivAt_X ⟨by linarith [hx.1],by linarith [hx.2]⟩).sub_const (1/2)).fun_add
        ((hasDerivAt_id' x).const_mul (12/13))).congr_deriv (by ring)
    · intro x hx
      have hx' : s0 ≤ x ∧ x ≤ td := ⟨by linarith [hx.1],by linarith [hx.2]⟩
      have hb := circle_bounds hx'
      have he := (circle_identities hx').2.2
      have hZ := Z_pos hx'
      have hle : Y x/Z x ≤ 12/13 := (div_le_iff₀ hZ).mpr (by linarith [hb.2.2.1])
      linarith
  have h := hm ⟨le_rfl,hts⟩ ⟨hts,le_rfl⟩ hts
  dsimp [f] at h
  linarith

lemma target_at_upper_side (t : ℝ) (ht : s0 ≤ t ∧ t ≤ Real.pi/4) :
    label (sideTopA t) (sideTopU t)=side (sideTopA t) (sideTopU t) := by
  have hlabel := (sideTop_state ht).2
  rw [hlabel]
  symm
  by_cases hs : t ≤ td
  · simp only [sideTopA,sideTopU,ite_eq_left hs]
    exact circle_label ⟨ht.1,hs⟩
  · simp only [sideTopA,sideTopU,ite_eq_right hs]
    exact (diagonal_state ⟨(lt_of_not_ge hs).le,ht.2⟩).2.2

lemma side_radial_upper {a u : ℝ} (h : Admissible a u)
    (hT : label a u=side a u) : a ≤ sideTopA (label a u) := by
  have hs := side_segment h hT
  have ht : s0 ≤ label a u ∧ label a u ≤ Real.pi/4 :=
    ⟨(side_state_transition_bounds h hT).2.2,h.label_le_quarter⟩
  have htop := side_segment (sideTop_state ht).1 (target_at_upper_side _ ht)
  rw [(sideTop_state ht).2] at htop
  linarith [hs.2.1,hs.2.2,htop.2.2]

end Boundary
end SquaresInCircles.Seven
