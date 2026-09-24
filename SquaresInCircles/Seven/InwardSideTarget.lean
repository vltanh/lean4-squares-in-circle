import SquaresInCircles.Seven.BoundarySegments
import SquaresInCircles.Seven.EasySectors

/-!
# The inward axis, positive signs, side target

The support is concave in the source label, so the endpoints `0` and `π/4`
suffice.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

private def targetH (A v s t : ℝ) : ℝ :=
  (A+1/2)*Real.cos (gap+t-s)+(1/2-v)*Real.sin (gap+t-s)

private lemma target_angle {A v t : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (ht : 0 ≤ t ∧ t ≤ Real.pi/4) :
    0 < gap+t-label A v ∧ gap+t-label A v < Real.pi/2 := by
  have hs0 := side_selected_label_gt h hT
  have hs1 := h.label_le_quarter
  dsimp [gap]
  constructor <;> linarith [ht.1,ht.2,pi_lt_22_over_7,Real.pi_pos]

private lemma targetH_support {A v t : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (ht : 0 ≤ t ∧ t ≤ Real.pi/4) :
    support A v (2*Real.pi-gap-t+label A v)=targetH A v (label A v) t := by
  have hd := target_angle h hT ht
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1.le (by linarith [hd.2,Real.pi_pos])
  have hc0 := cos_nonneg_quarter ⟨by linarith [hd.1,Real.pi_pos],hd.2.le⟩
  have he : 2*Real.pi-gap-t+label A v=2*Real.pi-(gap+t-label A v) := by ring
  rw [he]
  simp only [support,cos_two_pi_sub,Real.sin_two_pi_sub,abs_neg,abs_of_nonneg hs0,
    abs_of_nonneg hc0,targetH]
  ring

private lemma targetH_pos {A v t : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) (ht : 0 ≤ t ∧ t ≤ Real.pi/4) :
    0 < targetH A v (label A v) t := by
  have hsigned : signedLabel A v=label A v := by
    simp [signedLabel,not_lt_of_ge h.1,abs_of_nonneg h.1]
  have hpoint : |(label A v-1/2)-signedLabel A v| ≤ 801/1600 := by
    rw [hsigned]
    norm_num
  have hm := marker_arc_support
    (show Admissible A |v| by simpa only [abs_of_nonneg h.1] using h)
    hpoint (2*Real.pi-gap-t+label A v)
  have he : 2*Real.pi-gap-t+label A v-(label A v-1/2)=2*Real.pi-(gap+t-1/2) := by ring
  rw [he,cos_two_pi_sub,targetH_support h hT ht] at hm
  have hp : 0 < Real.cos (gap+t-1/2) := Real.cos_pos_of_mem_Ioo
    ⟨by dsimp [gap]; linarith [ht.1,pi_lower_157],
     by dsimp [gap]; linarith [ht.2,pi_lt_22_over_7]⟩
  exact hp.trans_le hm

private lemma targetH_zero_gt_one {A v : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) : 1 < targetH A v (label A v) 0 := by
  let s := label A v
  let d := gap-s
  have hs : 9/25 < s ∧ s ≤ Real.pi/4 := ⟨side_selected_label_gt h hT,h.label_le_quarter⟩
  have hd : 0 < d ∧ d < Real.pi/2 := by
    dsimp [d,gap]; constructor <;> linarith [hs.1,hs.2,pi_lt_22_over_7,Real.pi_pos]
  have hc0 := cos_nonneg_quarter ⟨by linarith [hd.1,Real.pi_pos],hd.2.le⟩
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hd.1.le (by linarith [hd.2,Real.pi_pos])
  have hline : A ≥ Boundary.tieA s := by
    obtain ⟨h1,-,h3⟩ := Boundary.side_segment h hT
    have h1' : (4/5)*s ≤ v := h1
    have h3' : A=Boundary.tieA s+(4/9)*(v-(4/5)*s) := h3
    linarith
  have hvbound : v ≤ 1/2+(6/5)*(s-Real.pi/6) := by
    have hh := side_identity_transverse A v
    rw [← hT] at hh
    change s=_ at hh
    linarith [h.remainder_nonneg]
  have hH : targetH A v (label A v) 0=(A+1/2)*Real.cos d+(1/2-v)*Real.sin d := by
    dsimp only [targetH,d,s]; rw [add_zero]
  rw [hH]
  by_cases hs1 : s ≤ Real.pi/6
  · have hA : 19/20 < A := by dsimp [Boundary.tieA] at hline; linarith [pi_lower_157]
    have hv : v ≤ 1/2 := by linarith
    have hd7 : d < 7/10 := by dsimp [d,gap]; linarith [hs.1,pi_lt_22_over_7]
    have hcos : 151/200 < Real.cos d := by
      have hh := Real.one_sub_sq_div_two_le_cos (x := d)
      nlinarith
    have hm := mul_nonneg (show 0 ≤ 1/2-v by linarith) hsin0
    have hc : (29/20:ℝ)*(151/200) < (A+1/2)*Real.cos d := by gcongr; linarith
    nlinarith
  · by_cases hs2 : s ≤ 2/3
    · have hA : 4/5 < A := by dsimp [Boundary.tieA] at hline; linarith [pi_lower_157]
      have hv : v < 7/10 := by linarith [pi_lower_157]
      have hd6 : d ≤ Real.pi/6 := by dsimp [d,gap]; linarith
      have hcos : 17/20 < Real.cos d := by
        have hh := Real.strictAntiOn_cos.antitoneOn
          (show d ∈ Icc 0 Real.pi by constructor <;> linarith [hd.1,hd.2,Real.pi_pos])
          (show Real.pi/6 ∈ Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos]) hd6
        rw [Real.cos_pi_div_six] at hh
        linarith [sqrt_three_bounds.1]
      have hsin : Real.sin d ≤ 1/2 := by
        have hh := sin_le_sin_half
          ⟨by linarith [hd.1,Real.pi_pos],hd.2.le⟩
          ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩ hd6
        simpa only [Real.sin_pi_div_six] using hh
      have hm := mul_nonneg (show 0 ≤ 7/10-v by linarith) hsin0
      have hc : (13/10:ℝ)*(17/20) < (A+1/2)*Real.cos d := by gcongr; linarith
      nlinarith
    · have hA := side_selected_a_gt h hT
      have hv := h.u_lt
      have hdlim : d < 8/21 := by dsimp [d,gap]; linarith [pi_lt_22_over_7]
      have hcos : 409/441 < Real.cos d := by
        have hh := Real.one_sub_sq_div_two_le_cos (x := d)
        nlinarith
      have hsin : Real.sin d < 8/21 := (Real.sin_le hd.1.le).trans_lt hdlim
      have hm := mul_nonneg (show 0 ≤ 31/40-v by linarith) hsin0
      have hc : (6/5:ℝ)*(409/441) < (A+1/2)*Real.cos d := by gcongr; linarith
      nlinarith

private def quarterProfile (d : ℝ) : ℝ :=
  (3/2)*Real.cos (5*Real.pi/12-d)-d*((4/5)*Real.cos (5*Real.pi/12-d)+(6/5)*Real.sin (5*Real.pi/12-d))

private def quarterProfileD (d : ℝ) : ℝ :=
  (3/10)*Real.sin (5*Real.pi/12-d)-(4/5)*Real.cos (5*Real.pi/12-d)-
    d*((4/5)*Real.sin (5*Real.pi/12-d)-(6/5)*Real.cos (5*Real.pi/12-d))

private def quarterProfileDD (d : ℝ) : ℝ :=
  (9/10)*Real.cos (5*Real.pi/12-d)-(8/5)*Real.sin (5*Real.pi/12-d)+
    d*((4/5)*Real.cos (5*Real.pi/12-d)+(6/5)*Real.sin (5*Real.pi/12-d))

private lemma quarter_profile_gt {d : ℝ} (hd : -1/6 ≤ d ∧ d ≤ Real.pi/12) :
    (1:ℝ)/3 < quarterProfile d := by
  let f : ℝ → ℝ := fun x => quarterProfile x-1/3
  have d1 (x : ℝ) : HasDerivAt f (quarterProfileD x) x := by
    have harg : HasDerivAt (fun y : ℝ => 5*Real.pi/12-y) (-1) x :=
      (hasDerivAt_id' x).const_sub _
    exact (((harg.cos.const_mul (3/2)).fun_sub
      ((hasDerivAt_id' x).fun_mul ((harg.cos.const_mul (4/5)).fun_add
        (harg.sin.const_mul (6/5))))).sub_const (1/3)).congr_deriv
      (by simp only [quarterProfileD]; ring)
  have d2 (x : ℝ) : HasDerivAt quarterProfileD (quarterProfileDD x) x := by
    have harg : HasDerivAt (fun y : ℝ => 5*Real.pi/12-y) (-1) x :=
      (hasDerivAt_id' x).const_sub _
    exact (((harg.sin.const_mul (3/10)).fun_sub (harg.cos.const_mul (4/5))).fun_sub
      ((hasDerivAt_id' x).fun_mul ((harg.sin.const_mul (4/5)).fun_sub
        (harg.cos.const_mul (6/5))))).congr_deriv
      (by simp only [quarterProfileDD]; ring)
  have hdd (x : ℝ) (hx : x ∈ Icc (-1/6) (Real.pi/12)) : quarterProfileDD x ≤ 0 := by
    let z := 5*Real.pi/12-x
    have hz : Real.pi/3 ≤ z ∧ z ≤ Real.pi/2 := by
      dsimp [z]; constructor <;> linarith [hx.1,hx.2,pi_lower_157]
    have hC0 : 0 ≤ Real.cos z := cos_nonneg_quarter
      ⟨by linarith [hz.1,Real.pi_pos],hz.2⟩
    have hC : Real.cos z ≤ 1/2 := by
      have hh := Real.strictAntiOn_cos.antitoneOn
        (show Real.pi/3 ∈ Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
        (show z ∈ Icc 0 Real.pi by constructor <;> linarith [hz.1,hz.2,Real.pi_pos]) hz.1
      simpa only [Real.cos_pi_div_three] using hh
    have hS : 4/5 < Real.sin z := by
      have hh := sin_le_sin_half
        (x := Real.pi/3) (y := z)
        (by constructor <;> linarith [Real.pi_pos])
        (by constructor <;> linarith [hz.1,hz.2,Real.pi_pos]) hz.1
      rw [Real.sin_pi_div_three] at hh
      linarith [sqrt_three_bounds.1]
    have h0 : 0 ≤ (4/5)*Real.cos z+(6/5)*Real.sin z := by positivity
    have h1 : (4/5)*Real.cos z+(6/5)*Real.sin z ≤ 8/5 := by linarith [Real.sin_le_one z]
    have hp := mul_nonneg (show 0 ≤ 4/15-x by linarith [hx.2,pi_lt_22_over_7]) h0
    dsimp [quarterProfileDD]
    change (9/10)*Real.cos z-(8/5)*Real.sin z+x*((4/5)*Real.cos z+(6/5)*Real.sin z) ≤ 0
    nlinarith
  have hlo : 0 < f (-1/6) := by
    let e := Real.pi/12-1/6
    have he : 9/100 < e ∧ e < 1/10 := by dsimp [e]; constructor <;> linarith [pi_lower_157,pi_lt_22_over_7]
    have hs := Real.sin_ge_sub_cube (show 0 ≤ e by linarith)
    have hc := Real.one_sub_sq_div_two_le_cos (x := e)
    have he3 : e^3 ≤ (1/10:ℝ)^3 := pow_le_pow_left₀ (by linarith) he.2.le 3
    have hid : quarterProfile (-1/6)=(49/30)*Real.sin e+(1/5)*Real.cos e := by
      have hang : 5*Real.pi/12-(-1/6)=Real.pi/2-e := by dsimp [e]; ring
      dsimp [quarterProfile]
      rw [hang,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
      ring
    dsimp [f]
    rw [hid]
    nlinarith
  have hhi : 0 < f (Real.pi/12) := by
    have hid : quarterProfile (Real.pi/12)=3/4-Real.pi*(1/30+Real.sqrt 3/20) := by
      dsimp [quarterProfile]
      rw [show 5*Real.pi/12-Real.pi/12=Real.pi/3 by ring,
        Real.cos_pi_div_three,Real.sin_pi_div_three]
      ring
    have hp := mul_lt_mul_of_pos_left sqrt_three_bounds.2 Real.pi_pos
    have hp' := mul_lt_mul_of_pos_right pi_lt_22_over_7 (show (0:ℝ) < 1/30+(1733/1000)/20 by norm_num)
    dsimp [f]
    rw [hid]
    nlinarith
  have hh := positive_of_second_nonpos hd
    (by dsimp [f,quarterProfile]; fun_prop)
    (by unfold quarterProfileD; fun_prop)
    (fun x _ => d1 x) (fun x _ => d2 x) hdd hlo hhi
  dsimp [f] at hh
  linarith

private lemma targetH_quarter_gt {A v : ℝ} (h : Admissible A v)
    (hT : label A v=side A v) :
    (1:ℝ)/3 < targetH A v (label A v) (Real.pi/4) := by
  let d := label A v-Real.pi/6
  let z := 5*Real.pi/12-d
  have hd : -1/6 ≤ d ∧ d ≤ Real.pi/12 := by
    have hs := side_selected_label_gt h hT
    have hq := h.label_le_quarter
    dsimp [d]
    constructor <;> linarith [pi_lt_22_over_7]
  have hz : Real.pi/3 ≤ z ∧ z ≤ Real.pi/2 := by
    dsimp [z]; constructor <;> linarith [hd.1,hd.2,pi_lower_157]
  have hsin : 4/5 < Real.sin z := by
    have hh := sin_le_sin_half (x := Real.pi/3) (y := z)
      (by constructor <;> linarith [Real.pi_pos])
      (by constructor <;> linarith [hz.1,hz.2,Real.pi_pos]) hz.1
    rw [Real.sin_pi_div_three] at hh
    linarith [sqrt_three_bounds.1]
  have hcoef : 0 ≤ (3/10)*Real.sin z-(2/15)*Real.cos z := by
    linarith [Real.cos_le_one z]
  have hx := side_identity_radial A v
  have hy := side_identity_transverse A v
  rw [← hT] at hx hy
  have hid : targetH A v (label A v) (Real.pi/4)=quarterProfile d+
      remainder A v*((3/10)*Real.sin z-(2/15)*Real.cos z) := by
    have he : gap+Real.pi/4-label A v=z := by dsimp [z,d,gap]; ring
    dsimp [targetH]
    rw [he]
    dsimp [quarterProfile,z,d] at *
    nlinarith
  rw [hid]
  exact (quarter_profile_gt hd).trans_le
    (le_add_of_nonneg_right (mul_nonneg h.remainder_nonneg hcoef))

/-- Whole-domain support certificate; there is no hypothesis on the source's
active label or center beyond its ordinary admissibility. -/
theorem fixed_gap_inward_side_target {a u A v : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label A v=side A v) :
    0 < pairSupport a u A v .positive .positive 2 gap := by
  let s := label A v
  let f : ℝ → ℝ := fun t => 1/2-(1+2*Real.pi/15)+(4/5)*t+targetH A v s t
  let df : ℝ → ℝ := fun t => 4/5-(A+1/2)*Real.sin (gap+t-s)+(1/2-v)*Real.cos (gap+t-s)
  let ddf : ℝ → ℝ := fun t => -targetH A v s t
  have hd (t : ℝ) : HasDerivAt f (df t) t := by
    have ha : HasDerivAt (fun x : ℝ => gap+x-s) 1 t :=
      ((hasDerivAt_id' t).const_add gap).sub_const s
    exact (((hasDerivAt_const t (1/2-(1+2*Real.pi/15))).fun_add
      ((hasDerivAt_id' t).const_mul (4/5))).fun_add
      ((ha.cos.const_mul (A+1/2)).fun_add (ha.sin.const_mul (1/2-v)))).congr_deriv
      (by simp only [df]; ring)
  have hdd (t : ℝ) : HasDerivAt df (ddf t) t := by
    have ha : HasDerivAt (fun x : ℝ => gap+x-s) 1 t :=
      ((hasDerivAt_id' t).const_add gap).sub_const s
    exact (((hasDerivAt_const t (4/5)).fun_sub (ha.sin.const_mul (A+1/2))).fun_add
      (ha.cos.const_mul (1/2-v))).congr_deriv (by simp only [ddf,targetH]; ring)
  have hm (t : ℝ) (ht : t ∈ Icc 0 (Real.pi/4)) : ddf t ≤ 0 := by
    have hh := targetH_pos h' hT ht
    dsimp [ddf,s]
    linarith
  have hlo : 0 < f 0 := by
    have hh := targetH_zero_gt_one h' hT
    dsimp [f,s]
    linarith [pi_lt_22_over_7]
  have hhi : 0 < f (Real.pi/4) := by
    have hh := targetH_quarter_gt h' hT
    dsimp [f,s]
    linarith [pi_lower_157]
  have hf := positive_of_second_nonpos
    ⟨h.label_nonneg,h.label_le_quarter⟩
    (by dsimp [f,targetH]; fun_prop) (by dsimp [df]; fun_prop)
    (fun t _ => hd t) (fun t _ => hdd t) hm hlo hhi
  rw [pairSupport_two]
  simp only [TransverseSign.coe,one_mul]
  rw [targetH_support h' hT ⟨h.label_nonneg,h.label_le_quarter⟩]
  dsimp [f,s] at hf
  linarith [h.radial_label_bound]

end SquaresInCircles.Seven
