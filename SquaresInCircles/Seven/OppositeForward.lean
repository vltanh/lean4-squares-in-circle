import SquaresInCircles.Seven.ForwardPositive
import SquaresInCircles.Seven.CapReduction
import SquaresInCircles.Seven.SideSide
import SquaresInCircles.Seven.PolynomialCertificates

/-!
# Forward transverse source with signs (-,+)

All four axial/side combinations are treated on their full admissible domains.
Capped labels are eliminated separately by `CapReduction`.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma pairSupport_forward_opposite {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v) :
    pairSupport a u A v .negative .positive 1 gap =
      sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  have hc : 0 ≤ Real.cos w := cos_nonneg_quarter
    ⟨by linarith [hw.1,Real.pi_pos],by linarith [hw.2,Real.pi_pos]⟩
  rw [pairSupport_one]
  simp only [TransverseSign.coe,neg_one_mul,one_mul,sub_neg_eq_add]
  have he : 3*Real.pi/2-gap+label a u+label A v = 3*Real.pi/2+w := by
    dsimp [w]
    ring
  rw [he]
  have hc' : Real.cos (3*Real.pi/2+w)=Real.sin w := by
    rw [show 3*Real.pi/2+w=Real.pi+(Real.pi/2+w) by ring]
    simp [Real.cos_add,Real.sin_add]
  have hs' : Real.sin (3*Real.pi/2+w)=-Real.cos w := by
    rw [show 3*Real.pi/2+w=Real.pi+(Real.pi/2+w) by ring]
    simp [Real.cos_add,Real.sin_add]
  change _ = sideSideSupport u A v w
  simp only [support,hc',hs',abs_neg,abs_of_nonneg hc,sideSideSupport]
  ring

lemma forward_turn_nonneg {w : ℝ} (hw : 0 ≤ w ∧ w ≤ Real.pi/6) :
    0 ≤ Real.sin w-(4/5)*w-(1/2)*(1-Real.cos w) := by
  have hlim : w ≤ 8/15 := by linarith [hw.2,pi_upper_22]
  have hs := Real.sin_ge_sub_cube hw.1
  have hc := Real.one_sub_sq_div_two_le_cos (x := w)
  have hsq : w^2 ≤ (8/15 : ℝ)^2 := by nlinarith [hw.1]
  have hp : 0 ≤ 1/5-w/4-w^2/6 := by nlinarith
  have hm := mul_nonneg hw.1 hp
  nlinarith

lemma opposite_support_positive_turn {u A v w : ℝ}
    (hA : 1/2 ≤ A) (hv : 0 ≤ v) (hw : 0 ≤ w ∧ w ≤ Real.pi/6) :
    1-u-v+Real.sin w-(1/2)*(1-Real.cos w) ≤ sideSideSupport u A v w := by
  have hs : 0 ≤ Real.sin w := Real.sin_nonneg_of_nonneg_of_le_pi hw.1
    (by linarith [hw.2,Real.pi_pos])
  have hc : 0 ≤ 1-Real.cos w := sub_nonneg.mpr (Real.cos_le_one w)
  have hp := mul_nonneg (show 0 ≤ A-1/2 by linarith) hs
  have hp' := mul_nonneg hv hc
  dsimp [sideSideSupport]
  rw [abs_of_nonneg hs]
  nlinarith

lemma opposite_support_negative_turn {u A v z : ℝ}
    (h' : Admissible A v) (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    1-u-v-(A-1/2)*Real.sin z-(1/2)*(1-Real.cos z) ≤
      sideSideSupport u A v (-z) := by
  have hs : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
    (by linarith [hz.2,Real.pi_pos])
  have hc : 0 ≤ 1-Real.cos z := sub_nonneg.mpr (Real.cos_le_one z)
  have hp := mul_nonneg h'.1 hc
  dsimp [sideSideSupport]
  rw [Real.sin_neg,Real.cos_neg,abs_neg,abs_of_nonneg hs]
  nlinarith

lemma opposite_axial_scalar {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/3) :
    0 < 1-4*Real.pi/15+(4/5)*z-(Real.sqrt 3-1)*Real.sin z
      -(1/2)*(1-Real.cos z) := by
  have hz1 : z ≤ 11/10 := by linarith [hz.2,pi_upper_22]
  have hp := axialPairPolynomial_pos ⟨hz.1,hz1⟩
  have c0 : 0 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have cL : 7/10 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have cU : Real.sqrt 3-1 ≤ 3/4 := by linarith [sqrt_three_bounds.2]
  have hs := mul_le_mul_of_nonneg_left (sin_upper_five hz.1) c0
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  have h1 := mul_nonneg hz.1 (show 0 ≤ 3/4-(Real.sqrt 3-1) by linarith)
  have h3 := mul_nonneg (pow_nonneg hz.1 3)
    (show 0 ≤ Real.sqrt 3-1-7/10 by linarith)
  have h5 := mul_nonneg (pow_nonneg hz.1 5)
    (show 0 ≤ 3/4-(Real.sqrt 3-1) by linarith)
  dsimp [axialPairPolynomial] at hp
  nlinarith [pi_upper_22]

lemma opposite_axial_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u=axial u) (hB : label A v=axial v) :
    0 < sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  have he : u+v=(4/5)*(gap+w) := by
    dsimp [w]
    rw [hA,hB]
    dsimp [axial]
    ring
  change 0 < sideSideSupport u A v w
  by_cases hpos : 0 ≤ w
  · have hl := opposite_support_positive_turn (u := u) h'.2.2.1 h'.1 ⟨hpos,hw.2⟩
    have hr := forward_turn_nonneg ⟨hpos,hw.2⟩
    dsimp [gap] at he
    linarith [pi_upper_22]
  · let z := -w
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by
      dsimp [z]
      constructor <;> linarith [hw.1]
    have hl := opposite_support_negative_turn (u := u) h' hz
    have hr := opposite_axial_scalar hz
    have hs : 0 ≤ Real.sin z := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    have hm := mul_nonneg (show 0 ≤ Real.sqrt 3-1-(A-1/2) by
      linarith [h'.a_le_sqrt_three]) hs
    have hwz : w = -z := by dsimp [z]; ring
    rw [hwz]
    rw [hwz] at he
    dsimp [gap] at he
    nlinarith

def mixedMargin : ℝ := 32/15-2*Real.pi/15-Real.sqrt 2626/30

lemma mixedMargin_gt : (1 : ℝ)/168 < mixedMargin := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2626 by norm_num)
  have hn := Real.sqrt_nonneg (2626 : ℝ)
  have hupper : Real.sqrt 2626 < 205/4 := by nlinarith
  dsimp [mixedMargin]
  linarith [pi_upper_22]

lemma mixed_linear_bound {a u : ℝ} (h : Admissible a u) :
    (3/5)*a+(11/15)*u ≤ Real.sqrt 2626/30-2/3 := by
  have hh := dot_lower_candidate (p := -(3/5)) (r := -(11/15)) h.2.2.2
  have he : radius*Real.sqrt (((3/5 : ℝ)^2+(11/15)^2)) = Real.sqrt 2626/30 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (3/5)^2+(11/15)^2 by norm_num)
    have hs' := Real.sq_sqrt (show (0 : ℝ) ≤ 2626 by norm_num)
    have hn : 0 ≤ radius*Real.sqrt (((3/5 : ℝ)^2+(11/15)^2)) := by
      exact mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
    have hsq : (radius*Real.sqrt (((3/5 : ℝ)^2+(11/15)^2)))^2 =
        (Real.sqrt 2626/30)^2 := by
      rw [mul_pow,radius_sq,hs,div_pow (Real.sqrt 2626),hs']
      norm_num
    nlinarith [Real.sqrt_nonneg (2626 : ℝ)]
  simp only [neg_sq] at hh
  have hn : -radius*Real.sqrt (((3/5 : ℝ)^2+(11/15)^2)) = -(Real.sqrt 2626/30) := by
    nlinarith [he]
  rw [hn] at hh
  nlinarith

lemma mixed_clearance_bound {a u A v : ℝ}
    (h' : Admissible A v)
    (hA : label a u=axial u) (hT : label A v=side A v) :
    mixedMargin-(4/5)*(label a u+label A v-gap) ≤ 1-u-v := by
  have hl := mixed_linear_bound h'
  rw [hA,hT]
  dsimp [mixedMargin,axial,side,gap]
  linarith

lemma mixed_clearance_bound_swap {a u A v : ℝ}
    (h : Admissible a u)
    (hT : label a u=side a u) (hA : label A v=axial v) :
    mixedMargin-(4/5)*(label a u+label A v-gap) ≤ 1-u-v := by
  have hh := mixed_clearance_bound h hA hT
  linarith

lemma mixed_positive_turn {u A v w : ℝ}
    (h' : Admissible A v) (hw : 0 ≤ w ∧ w ≤ Real.pi/6)
    (hclear : mixedMargin-(4/5)*w ≤ 1-u-v) :
    0 < sideSideSupport u A v w := by
  have hl := opposite_support_positive_turn (u := u) h'.2.2.1 h'.1 hw
  have hr := forward_turn_nonneg hw
  linarith [mixedMargin_gt]

lemma side_axial_far_profile {z : ℝ} (hz : 1/3 ≤ z ∧ z ≤ 7/10) :
    0 < 1/2-Real.pi/5+(6/5)*z-(Real.sqrt 3-1)*Real.sin z
      -(1/2)*(1-Real.cos z) := by
  let B : ℝ → ℝ := fun x => 1/2-Real.pi/5+(6/5)*x-
    (Real.sqrt 3-1)*Real.sin x-(1/2)*(1-Real.cos x)
  have hc0 : 0 ≤ Real.sqrt 3-1 := by linarith [sqrt_three_bounds.1]
  have hc1 : Real.sqrt 3-1 < 11/15 := by linarith [sqrt_three_bounds.2]
  have hm : MonotoneOn B (Icc (1/3) (7/10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by dsimp [B]; fun_prop)
    · exact Differentiable.differentiableOn (by dsimp [B]; fun_prop)
    · intro x hx
      have hx' : x ∈ Icc (1/3 : ℝ) (7/10) := interior_subset hx
      have hsin := Real.sin_le (show 0 ≤ x by linarith [hx'.1])
      have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one x) hc0
      have hd : deriv B x = 6/5-(Real.sqrt 3-1)*Real.cos x-(1/2)*Real.sin x := by
        simp (disch := fun_prop) [B]
      rw [hd]
      linarith [hx'.2]
  have hb : 0 < B (1/3) := by
    have hsin := sin_upper_five (show (0 : ℝ) ≤ 1/3 by norm_num)
    have hcos := Real.one_sub_sq_div_two_le_cos (x := (1/3 : ℝ))
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi
      (show (0 : ℝ) ≤ 1/3 by norm_num) (by linarith [pi_lower_157])
    have hp := mul_nonneg (show 0 ≤ 11/15-(Real.sqrt 3-1) by linarith) hsin0
    dsimp [B]
    nlinarith [pi_upper_22]
  exact hb.trans_le (hm (by constructor <;> norm_num) hz hz.1)

lemma opposite_axial_side_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hA : label a u=axial u) (hT : label A v=side A v) :
    0 < sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  have hclear := mixed_clearance_bound h' hA hT
  change mixedMargin-(4/5)*w ≤ 1-u-v at hclear
  change 0 < sideSideSupport u A v w
  by_cases hpos : 0 ≤ w
  · exact mixed_positive_turn h' ⟨hpos,hw.2⟩ hclear
  · let z := -w
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by dsimp [z]; constructor <;> linarith [hw.1]
    have hz7 : z < 7/10 := by
      have ht := side_selected_label_gt h' hT
      have ha := h.label_nonneg
      dsimp [z,w,gap]
      linarith [pi_upper_22]
    have hl := opposite_support_negative_turn (u := u) h' hz
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    have hsin := Real.sin_le hz.1
    have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
    have hA1 := side_selected_a_lt h' hT
    have hp := mul_nonneg (show 0 ≤ 5/8-(A-1/2) by linarith) hsin0
    have hq := mul_nonneg hz.1 (show 0 ≤ 7/40-z/4 by linarith)
    have he : w = -z := by dsimp [z]; ring
    rw [he]
    rw [he] at hclear
    nlinarith [mixedMargin_gt]

lemma opposite_side_axial_pos {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v) :
    0 < sideSideSupport u A v (label a u+label A v-gap) := by
  let w := label a u+label A v-gap
  have hw : -Real.pi/3 ≤ w ∧ w ≤ Real.pi/6 := by
    have h0 := h.label_nonneg
    have h1 := h'.label_nonneg
    have h2 := h.label_le_quarter
    have h3 := h'.label_le_quarter
    dsimp [w,gap]
    constructor <;> linarith
  have hclear := mixed_clearance_bound_swap h hT hA
  change mixedMargin-(4/5)*w ≤ 1-u-v at hclear
  change 0 < sideSideSupport u A v w
  by_cases hpos : 0 ≤ w
  · exact mixed_positive_turn h' ⟨hpos,hw.2⟩ hclear
  · let z := -w
    have hz : 0 ≤ z ∧ z ≤ Real.pi/3 := by dsimp [z]; constructor <;> linarith [hw.1]
    have hz7 : z < 7/10 := by
      have ht := side_selected_label_gt h hT
      have ha := h'.label_nonneg
      dsimp [z,w,gap]
      linarith [pi_upper_22]
    have he : w = -z := by dsimp [z]; ring
    rw [he]
    rw [he] at hclear
    have hl := opposite_support_negative_turn (u := u) h' hz
    have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1
      (by linarith [hz.2,Real.pi_pos])
    have hA1 := h'.a_le_sqrt_three
    have hp := mul_nonneg (show 0 ≤ Real.sqrt 3-1-(A-1/2) by linarith) hsin0
    by_cases hzsmall : z ≤ 1/3
    · have hsin := Real.sin_le hz.1
      have hcos := Real.one_sub_sq_div_two_le_cos (x := z)
      have hq := mul_nonneg hz.1 (show 0 ≤ 1/3-z by linarith)
      have hpc := mul_nonneg
        (show 0 ≤ 11/15-(Real.sqrt 3-1) by linarith [sqrt_three_bounds.2]) hsin0
      nlinarith [mixedMargin_gt]
    · have hsource := side_identity_transverse a u
      rw [← hT] at hsource
      have hu : u ≤ 1/2+(6/5)*(label a u-Real.pi/6) := by
        linarith [h.remainder_nonneg]
      have hv : v=(4/5)*label A v := by rw [hA]; dsimp [axial]; ring
      have hs : 1/2-Real.pi/5+(6/5)*z ≤ 1-u-v := by
        have hw' : label a u+label A v=gap-z := by
          dsimp [z,w]
          ring
        have ht := h'.label_nonneg
        dsimp [gap] at hw'
        linarith
      have hprof := side_axial_far_profile ⟨(lt_of_not_ge hzsmall).le,hz7.le⟩
      nlinarith

/-- Complete A/T sector, including the only possible side--side equality. -/
theorem fixed_gap_forward_opposite_active {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v) :
    PairProperty a u A v .negative .positive 1 := by
  unfold PairProperty
  rw [pairSupport_forward_opposite h h']
  rcases ha with hA | hT <;> rcases hb with hA' | hT'
  · have hp := opposite_axial_axial_pos h h' hA hA'
    exact ⟨hp.le,fun _ _ => hp⟩
  · have hp := opposite_axial_side_pos h h' hA hT'
    exact ⟨hp.le,fun _ _ => hp⟩
  · have hp := opposite_side_axial_pos h h' hT hA'
    exact ⟨hp.le,fun _ _ => hp⟩
  · have hr : -Real.pi/3 ≤ label a u+label A v-gap ∧
        label a u+label A v-gap ≤ Real.pi/6 := by
      have h0 := h.label_nonneg
      have h1 := h'.label_nonneg
      have h2 := h.label_le_quarter
      have h3 := h'.label_le_quarter
      dsimp [gap]
      constructor <;> linarith
    refine ⟨sideSide_support_nonneg h h' (by rw [hT,hT']) hr,?_⟩
    intro hs hs'
    exact sideSide_support_pos hs h' hT hT'

end SquaresInCircles.Seven
