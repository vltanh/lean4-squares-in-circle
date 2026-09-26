import SquaresInCircles.Seven.BoundarySegments
import SquaresInCircles.Seven.PolynomialCertificates
import SquaresInCircles.Seven.AnalyticOrder

/-!
# Monotonicity of the target support on the axial boundary

On the circular piece by the sign of a derivative ratio, which reduces to a
polynomial certificate; on the straight piece by a sine/cosine comparison.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def axialX (s : ℝ) : ℝ := Real.sqrt (targetSq-(1/2+(4/5)*s)^2)
def axialY (s : ℝ) : ℝ := 1/2+(4/5)*s
def ratio (s : ℝ) : ℝ :=
  axialX s*(9/5-axialX s)/(axialY s*(axialX s-4/5))
def ratioD (s : ℝ) : ℝ :=
  4*(25*(axialX s)^4-65*(axialX s)^3+25*(axialX s)^2*(axialY s)^2+
    36*(axialX s)^2-40*axialX s*(axialY s)^2+36*(axialY s)^2)/
    (5*axialX s*(axialY s)^2*(5*axialX s-4)^2)

def circleTarget (t s : ℝ) : ℝ :=
  -(axialX s-1)*Real.sin (gap-t+s)+axialY s*Real.cos (gap-t+s)
def lineTarget (t s : ℝ) : ℝ :=
  -(tieA s-1/2)*Real.sin (gap-t+s)+((4/5)*s+1/2)*Real.cos (gap-t+s)
def vertexTarget (t s : ℝ) : ℝ :=
  -(sideTopA s-1/2)*Real.sin (gap-t+s)+(sideTopU s+1/2)*Real.cos (gap-t+s)

def switchAngle : ℝ := Real.arctan (9/4)
def switchLabel (t : ℝ) : ℝ := switchAngle-gap+t

lemma axial_circle_bounds {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) :
    (8:ℝ)/5 < axialX s ∧ axialX s < 7/4 ∧
    (1:ℝ)/2 ≤ axialY s ∧ axialY s ≤ Y0 ∧
    (axialX s)^2+(axialY s)^2=targetSq := by
  have hu : 0 ≤ (4/5)*s ∧ (4/5)*s ≤ u0 := by dsimp [s0] at hs; constructor <;> linarith [hs.1,hs.2]
  have huR : (4/5)*s ≤ rd := by linarith [hu.2,transition_coarse.2.2.2.1,rd_bounds.1]
  have hstate := circle_state ⟨hu.1,huR⟩
  have ho := circle_order hu.1 hu.2 (by linarith [transition_coarse.2.2.2.1,rd_bounds.1])
  rw [circle_u0] at ho
  have he : axialX s=circle ((4/5)*s)+1/2 := by dsimp [axialX,circle]; ring_nf
  have hey : axialY s=(4/5)*s+1/2 := by dsimp [axialY]; ring
  have hnorm := circle_eq ⟨hu.1,huR⟩
  rw [he,hey]
  have ha := transition_coarse
  have hbound := hstate.a_le_sqrt_three_sub_half
  exact ⟨by linarith,by linarith [sqrt_three_bounds.2],by linarith,
    by dsimp [u0] at hu; linarith,by simpa [add_comm] using hnorm⟩

lemma hasDerivAt_axialY (s : ℝ) : HasDerivAt axialY (4/5) s := by
  convert ((hasDerivAt_id s).const_mul (4/5)).const_add (1/2) using 1
  · rfl
  · ring

lemma hasDerivAt_axialX {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) :
    HasDerivAt axialX (-(4/5)*axialY s/axialX s) s := by
  have hb := axial_circle_bounds hs
  have hp : 0 < targetSq-(axialY s)^2 := by nlinarith [hb.2.2.2.2]
  have hd := ((hasDerivAt_const s targetSq).sub ((hasDerivAt_axialY s).pow 2)).sqrt (ne_of_gt hp)
  convert hd using 1
  · rfl
  · dsimp [axialX,axialY]
    field_simp
    ring

lemma hasDerivAt_ratio {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) :
    HasDerivAt ratio (ratioD s) s := by
  have hb := axial_circle_bounds hs
  have hx : axialX s ≠ 0 := by linarith [hb.1]
  have hy : axialY s ≠ 0 := by linarith [hb.2.2.1]
  have hden : axialY s*(axialX s-4/5) ≠ 0 := mul_ne_zero hy (by linarith [hb.1])
  have hd := ((hasDerivAt_axialX hs).mul
    ((hasDerivAt_axialX hs).const_sub (9/5))).div
    ((hasDerivAt_axialY s).mul ((hasDerivAt_axialX hs).sub_const (4/5))) hden
  convert hd using 1
  · rfl
  · dsimp [ratioD]
    field_simp [hx,hy,show axialX s-4/5 ≠ 0 by linarith [hb.1],
      show 5*axialX s-4 ≠ 0 by linarith [hb.1]]
    ring

lemma ratio_derivative_lt_one {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) : ratioD s < 1 := by
  have hb := axial_circle_bounds hs
  have hx : axialX s ≠ 0 := by linarith [hb.1]
  have hy : axialY s ≠ 0 := by linarith [hb.2.2.1]
  have hy2 : (axialY s)^2=13/4-(axialX s)^2 := by
    have hh := hb.2.2.2.2
    dsimp [targetSq] at hh
    linarith
  have hrad : 0 < 13-4*(axialX s)^2 := by nlinarith [hb.2.2.1,hy2]
  have hpoly := axialRatioPolynomial_pos ⟨hb.1.le,hb.2.1.le⟩
  have hden : 0 < 5*axialX s*(5*axialX s-4)^2*(13-4*(axialX s)^2) :=
    mul_pos (mul_pos (by linarith [hb.1]) (pow_pos (by linarith [hb.1]) 2)) hrad
  have hid : 1-ratioD s = axialRatioPolynomial (axialX s)/
      (5*axialX s*(5*axialX s-4)^2*(13-4*(axialX s)^2)) := by
    dsimp [ratioD]
    rw [hy2]
    dsimp [axialRatioPolynomial]
    field_simp [hx,show axialX s*5-4 ≠ 0 by linarith [hb.1],
      ne_of_gt hrad,show 13/4-(axialX s)^2 ≠ 0 by linarith]
    ring
  have hp := div_pos hpoly hden
  linarith

lemma ratio_nonneg {s : ℝ} (hs : 0 ≤ s ∧ s ≤ s0) : 0 ≤ ratio s := by
  have hb := axial_circle_bounds hs
  dsimp [ratio]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg (by linarith) (by linarith))

lemma ratio_zero_lt : ratio 0 < (51:ℝ)/200 := by
  have hr : (173:ℝ)/100 < Real.sqrt 3 ∧ Real.sqrt 3 < 17321/10000 := by
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    constructor <;> nlinarith [Real.sqrt_nonneg (3:ℝ)]
  have heX : axialX 0=Real.sqrt 3 := by norm_num [axialX,targetSq]
  have heY : axialY 0=1/2 := by norm_num [axialY]
  dsimp [ratio]
  rw [heX,heY]
  apply (div_lt_iff₀ (by linarith : 0 < (1/2:ℝ)*(Real.sqrt 3-4/5))).mpr
  linarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]

lemma circleTarget_decreases {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4) :
    AntitoneOn (circleTarget t) (Icc 0 s0) := by
  let E : ℝ → ℝ := fun s => Real.sin (gap-t+s)-ratio s*Real.cos (gap-t+s)
  have hangle (s : ℝ) (hs : s ∈ Icc 0 s0) :
      Real.pi/12 ≤ gap-t+s ∧ gap-t+s < Real.pi/2 := by
    have hc := transition_coarse
    dsimp [gap]
    constructor <;> linarith [ht.1,ht.2,hs.1,hs.2,pi_lt_22_over_7,Real.pi_pos]
  have hEder (s : ℝ) (hs : s ∈ Icc 0 s0) :
      HasDerivAt E ((1-ratioD s)*Real.cos (gap-t+s)+ratio s*Real.sin (gap-t+s)) s := by
    have hd : HasDerivAt (fun x : ℝ => gap-t+x) 1 s := (hasDerivAt_id s).const_add (gap-t)
    convert hd.sin.sub ((hasDerivAt_ratio hs).mul hd.cos) using 1
    ring
  have hEmono : MonotoneOn E (Icc 0 s0) := monoOn_of_hasDeriv_nonneg
    (fun s hs => (hEder s hs).continuousAt.continuousWithinAt)
    (fun s hs => hEder s ⟨hs.1.le,hs.2.le⟩)
    (fun s hs => by
      have hp := ratio_derivative_lt_one ⟨hs.1.le,hs.2.le⟩
      have hn := ratio_nonneg ⟨hs.1.le,hs.2.le⟩
      have ha := hangle s ⟨hs.1.le,hs.2.le⟩
      have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [ha.1,Real.pi_pos],ha.2.le⟩
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (x := gap-t+s)
        (by linarith [ha.1,Real.pi_pos]) (by linarith [ha.2,Real.pi_pos])
      exact add_nonneg (mul_nonneg (by linarith) hc) (mul_nonneg hn hh))
  have hE0 : 0 < E 0 := by
    have ha := hangle 0 ⟨le_rfl,by linarith [transition_coarse.2.2.2.2.1]⟩
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (x := Real.pi/12) (y := gap-t)
      (by linarith [Real.pi_pos]) (by simpa using ha.2.le) (by simpa using ha.1)
    have hl := Real.sin_ge_sub_cube (show 0 ≤ Real.pi/12 by positivity)
    have hc : (Real.pi/12)^3 ≤ (11/42:ℝ)^3 :=
      pow_le_pow_left₀ (by positivity) (by linarith [pi_lt_22_over_7]) 3
    have hR := ratio_nonneg (s := 0) ⟨le_rfl,by linarith [transition_coarse.2.2.2.2.1]⟩
    have hm := mul_le_mul_of_nonneg_left (Real.cos_le_one (gap-t)) hR
    dsimp [E]
    simp only [add_zero]
    linarith [ratio_zero_lt,pi_lower_157]
  have hEpos (s : ℝ) (hs : s ∈ Icc 0 s0) : 0 < E s :=
    hE0.trans_le (hEmono ⟨le_rfl,by linarith [transition_coarse.2.2.2.2.1]⟩ hs hs.1)
  have hder (s : ℝ) (hs : s ∈ Icc 0 s0) :
      HasDerivAt (circleTarget t)
        (-(axialY s*(axialX s-4/5)/axialX s)*E s) s := by
    have hd : HasDerivAt (fun x : ℝ => gap-t+x) 1 s := (hasDerivAt_id s).const_add (gap-t)
    have hx := hasDerivAt_axialX hs
    have hy := hasDerivAt_axialY s
    have hb := axial_circle_bounds hs
    convert (((hx.sub_const 1).neg.mul hd.sin).add (hy.mul hd.cos)) using 1
    · rfl
    · dsimp [E,ratio]
      field_simp [show axialX s ≠ 0 by linarith [hb.1],
        show axialY s ≠ 0 by linarith [hb.2.2.1],
        show axialX s*5-4 ≠ 0 by linarith [hb.1]]
      ring
  apply antiOn_of_hasDeriv_nonpos
    (fun s hs => (hder s hs).continuousAt.continuousWithinAt)
    (fun s hs => hder s ⟨hs.1.le,hs.2.le⟩)
  intro s hs
  have hb := axial_circle_bounds ⟨hs.1.le,hs.2.le⟩
  have hp := hEpos s ⟨hs.1.le,hs.2.le⟩
  have hcoef : 0 ≤ axialY s*(axialX s-4/5)/axialX s :=
    div_nonneg (mul_nonneg (by linarith [hb.2.2.1]) (by linarith [hb.1])) (by linarith [hb.1])
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoef) hp.le

lemma circleTarget_transition (t : ℝ) :
    circleTarget t s0=-(a0-1/2)*Real.sin (gap-t+s0)+Y0*Real.cos (gap-t+s0) := by
  have he : (4/5)*s0=u0 := by dsimp [s0]; ring
  have hx : axialX s0=a0+1/2 := by
    have hh := circle_u0
    dsimp [axialX]
    rw [he,add_comm (1/2:ℝ) u0]
    dsimp [circle] at hh
    linarith
  have hy : axialY s0=Y0 := by dsimp [axialY,s0,u0]; ring
  dsimp [circleTarget]
  rw [hx,hy]
  ring

lemma lineTarget_transition (t : ℝ) : lineTarget t s0=circleTarget t s0 := by
  have hl := transition_line
  have ha : tieA s0=a0 := by dsimp [tieA,s0]; linarith
  have hu : (4/5)*s0+1/2=Y0 := by dsimp [s0,u0]; ring
  rw [circleTarget_transition]
  dsimp [lineTarget]
  rw [ha,hu]

lemma switch_range : 0 < switchAngle ∧ switchAngle < Real.pi/2 := by
  exact ⟨Real.arctan_pos.mpr (by norm_num),Real.arctan_lt_pi_div_two _⟩

lemma switch_zero : Real.cos switchAngle-(4/9)*Real.sin switchAngle=0 := by
  dsimp [switchAngle]
  rw [Real.cos_arctan,Real.sin_arctan]
  ring

lemma switch_iff {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    0 ≤ Real.cos x-(4/9)*Real.sin x ↔ x ≤ switchAngle := by
  have hs := switch_range
  constructor
  · intro h
    by_contra hn
    have hlt : switchAngle < x := lt_of_not_ge hn
    have hsin := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [hs.1,Real.pi_pos]) hx.2 hlt
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hs.1.le
      (by linarith [hx.2,Real.pi_pos]) hlt.le
    linarith [switch_zero]
  · intro h
    have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [hx.1,Real.pi_pos]) hs.2.le h
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hx.1
      (by linarith [hs.2,Real.pi_pos]) h
    linarith [switch_zero]

lemma lineTarget_derivative_positive {t s : ℝ}
    (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4)
    (hs : s0 ≤ s ∧ s ≤ Real.pi/4)
    (hcut : s ≤ switchLabel t) :
    0 < (43/90-(4/5)*s)*Real.sin (gap-t+s)+(13/10-tieA s)*Real.cos (gap-t+s) := by
  let x := gap-t+s
  have hx : 0 < x ∧ x < Real.pi/2 := by
    have h0 := transition_coarse
    dsimp [x,gap]
    constructor <;> linarith [ht.1,ht.2,hs.1,hs.2,pi_lt_22_over_7,pi_lower_157]
  have hC : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1,Real.pi_pos],hx.2⟩
  have hS := Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2,Real.pi_pos])
  have hCS : Real.sin x ≤ (9/4)*Real.cos x := by
    have hq : x ≤ switchAngle := by dsimp [x,switchLabel] at *; linarith
    have hh := (switch_iff ⟨hx.1.le,hx.2.le⟩).mpr hq
    linarith
  have hA : tieA s < 9/8 := by
    have he : tieA s0=a0 := by dsimp [tieA,s0]; linarith [transition_line]
    have hh : tieA s ≤ tieA s0 := by dsimp [tieA]; linarith [hs.1]
    rw [he] at hh
    linarith [transition_coarse.2.1]
  by_cases hb : 0 ≤ 43/90-(4/5)*s
  · have hp := mul_nonneg hb hS
    have hpos := mul_pos (show 0 < 13/10-tieA s by linarith) hC
    dsimp [x] at *
    linarith
  · have hp := mul_nonneg (show 0 ≤ -(43/90-(4/5)*s) by linarith)
      (show 0 ≤ (9/4)*Real.cos x-Real.sin x by linarith)
    have hcoef : (91:ℝ)/360 ≤ (13/10-tieA s)+(9/4)*(43/90-(4/5)*s) := by
      dsimp [tieA]
      linarith [hs.2,pi_lt_22_over_7]
    have hpos := mul_pos (show 0 < (13/10-tieA s)+(9/4)*(43/90-(4/5)*s) by linarith) hC
    dsimp [x] at *
    linarith

lemma lineTarget_low_min {t s : ℝ}
    (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4)
    (hs : s0 ≤ s ∧ s ≤ Real.pi/4) (hcut : s ≤ switchLabel t) :
    circleTarget t s0 ≤ lineTarget t s := by
  have hm : MonotoneOn (lineTarget t) (Icc s0 s) := by
    apply monoOn_of_hasDeriv_nonneg
    · unfold lineTarget tieA; fun_prop
    · intro x hx
      have hd : HasDerivAt (fun y : ℝ => gap-t+y) 1 x := (hasDerivAt_id x).const_add (gap-t)
      have ha : HasDerivAt tieA (-(44/45)) x := by
        convert (hasDerivAt_const x ((2*Real.pi+7)/9)).sub
          ((hasDerivAt_id x).const_mul (44/45)) using 1
        · rfl
        · ring
      convert (((ha.sub_const (1/2)).neg.mul hd.sin).add
        ((((hasDerivAt_id x).const_mul (4/5)).add_const (1/2)).mul hd.cos)) using 1
      funext y; dsimp [lineTarget]
    · intro x hx
      have hp := lineTarget_derivative_positive ht
        ⟨hx.1.le,by linarith [hx.2,hs.2]⟩ (by linarith [hx.2,hcut])
      simp only [Pi.neg_apply,id]
      linarith
  rw [← lineTarget_transition]
  exact hm ⟨le_rfl,hs.1⟩ ⟨hs.1,le_rfl⟩ hs.1

end Boundary
end SquaresInCircles.Seven
