import SquaresInCircles.Seven.BoundaryPointChecks

/-!
# Positive scalar profiles after exact boundary minimization

The small-margin profile is proved by a uniform curvature lower bound and the
single fixed-point bounds from BoundaryPointChecks. The diagonal profile is
proved by monotonicity and elementary endpoint comparisons.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def transitionAngle (t : ℝ) : ℝ := gap-t+s0
def transitionF (t : ℝ) : ℝ :=
  1-Y t-(a0-1/2)*Real.sin (transitionAngle t)+Y0*Real.cos (transitionAngle t)
def transitionFD (t : ℝ) : ℝ :=
  -X t/Z t+(a0-1/2)*Real.cos (transitionAngle t)+Y0*Real.sin (transitionAngle t)
def transitionFDD (t : ℝ) : ℝ :=
  (3/4)*targetSq/(Z t)^3+(a0-1/2)*Real.sin (transitionAngle t)-Y0*Real.cos (transitionAngle t)

private lemma angle_derivative (t : ℝ) : HasDerivAt transitionAngle (-1) t := by
  convert (((hasDerivAt_const t gap).sub (hasDerivAt_id t)).add_const s0) using 1
  · rfl
  · ring

lemma hasDerivAt_transitionF {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt transitionF (transitionFD t) t := by
  have hd := (((hasDerivAt_Y ht).const_sub 1).sub
    ((angle_derivative t).sin.const_mul (a0-1/2))).add
    ((angle_derivative t).cos.const_mul Y0)
  convert hd using 1
  · rfl
  · dsimp [transitionFD]; ring

lemma hasDerivAt_transitionFD {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt transitionFD (transitionFDD t) t := by
  have hd := (((hasDerivAt_Y_prime ht).neg).add
    ((angle_derivative t).cos.const_mul (a0-1/2))).add
    ((angle_derivative t).sin.const_mul Y0)
  convert hd using 1
  · funext y; dsimp [transitionFD]; ring
  · dsimp [transitionFDD]; ring

lemma transition_curvature {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ td) :
    (3:ℝ)/8 < transitionFDD t := by
  have hs := transition_coarse
  have ht' : s0 ≤ t ∧ t ≤ td := ⟨by linarith,ht.2⟩
  have hb := circle_bounds ht'
  have hZ0 : 0 < Z t := by linarith [hb.2.2.2.2.2.1]
  have hZ3 : (Z t)^3 < (7/5:ℝ)^3 := by gcongr; exact hb.2.2.2.2.2.2
  have hlead : (7:ℝ)/8 < (3/4)*targetSq/(Z t)^3 := by
    apply (lt_div_iff₀ (pow_pos hZ0 3)).mpr
    dsimp [targetSq]
    nlinarith
  have hangle : Real.pi/6 < transitionAngle t ∧ transitionAngle t < Real.pi/2 := by
    dsimp [transitionAngle,gap]
    constructor <;> linarith [ht.1,ht.2,td_bounds.2,pi_upper_22,pi_lower_157]
  have hsin : 1/2 ≤ Real.sin (transitionAngle t) := by
    have hh := sin_le_sin_half
      (x := Real.pi/6) (y := transitionAngle t)
      (by constructor <;> linarith [Real.pi_pos])
      (by constructor <;> linarith [hangle.1,hangle.2,Real.pi_pos]) hangle.1.le
    simpa only [Real.sin_pi_div_six] using hh
  have hc0 : 0 ≤ Real.cos (transitionAngle t) := cos_nonneg_quarter
    ⟨by linarith [hangle.1,Real.pi_pos],hangle.2.le⟩
  have hlow : (3:ℝ)/10 < (a0-1/2)*Real.sin (transitionAngle t) := by
    have ha : (3:ℝ)/5 < a0-1/2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hsin) (show 0 ≤ a0-1/2 by linarith)]
  have hu : Y0*Real.cos (transitionAngle t) < (4:ℝ)/5 := by
    have hy : 0 ≤ Y0 ∧ Y0 < 4/5 := by dsimp [u0] at hs; constructor <;> linarith
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one (transitionAngle t)) hy.1
    linarith
  dsimp [transitionFDD]
  linarith

lemma transitionF_pos {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ td) : 0 < transitionF t := by
  have hs := transition_coarse
  have sub (x : ℝ) (hx : x ∈ Icc (2/5) td) : x ∈ Icc s0 td := ⟨by linarith [hx.1],hx.2⟩
  have htest : testLabel ∈ Icc (2/5) td := by
    dsimp [testLabel]
    exact ⟨by norm_num,td_bounds.1.le⟩
  have hf : ContinuousOn transitionF (Icc (2/5) td) := by
    intro x hx
    exact (hasDerivAt_transitionF (sub x hx)).continuousAt.continuousWithinAt
  have hdf : ContinuousOn transitionFD (Icc (2/5) td) := by
    intro x hx
    exact (hasDerivAt_transitionFD (sub x hx)).continuousAt.continuousWithinAt
  have hv : (3:ℝ)/4000 < transitionF testLabel := by
    simpa only [transitionF,transitionAngle,testValue,testAngle] using test_value_lower
  have hd : |transitionFD testLabel| < 1/400 := by
    simpa only [transitionFD,transitionAngle,testSlope,testAngle] using test_slope_bound
  exact positive_of_curvature_and_point ht htest hf hdf
    (fun x hx => hasDerivAt_transitionF (sub x hx))
    (fun x hx => hasDerivAt_transitionFD (sub x hx))
    (fun x hx => (transition_curvature hx).le) hv hd

def transitionDiagonalF (t : ℝ) : ℝ :=
  1/2-diagonal t-(a0-1/2)*Real.sin (transitionAngle t)+Y0*Real.cos (transitionAngle t)

lemma transitionDiagonalF_pos {t : ℝ} (ht : td ≤ t ∧ t ≤ Real.pi/4) :
    0 < transitionDiagonalF t := by
  have hs := transition_coarse
  have hmono : MonotoneOn transitionDiagonalF (Icc td (Real.pi/4)) := by
    apply monoOn_of_hasDeriv_nonneg
    · unfold transitionDiagonalF diagonal transitionAngle; fun_prop
    · intro x hx
      have ha := angle_derivative x
      have hdiag : HasDerivAt diagonal (-(12/5)) x := by
        convert ((((hasDerivAt_const x (2*Real.pi+7)).sub
          ((hasDerivAt_id x).const_mul 12))).div_const 5) using 1
        · rfl
        · ring
      convert (((hdiag.const_sub (1/2)).sub (ha.sin.const_mul (a0-1/2))).add
        (ha.cos.const_mul Y0)) using 1
      rfl
    · intro x hx
      have hang : 0 ≤ transitionAngle x ∧ transitionAngle x ≤ Real.pi/2 := by
        dsimp [transitionAngle,gap]
        constructor <;> linarith [hx.1,hx.2,td_bounds.1,pi_upper_22,pi_lower_157]
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hang.1 (by linarith [hang.2,Real.pi_pos])
      have hcos := cos_nonneg_quarter ⟨by linarith [hang.1,Real.pi_pos],hang.2⟩
      have hy0 : 0 ≤ Y0 := by dsimp [u0] at hs; linarith
      have ha0 : 0 ≤ a0-1/2 := by linarith
      linarith [mul_nonneg ha0 hcos,mul_nonneg hy0 hsin]
  have he : transitionDiagonalF td=transitionF td := by
    have hh := side_at_diagonal.2
    dsimp [sideU] at hh
    dsimp [transitionDiagonalF,transitionF,diagonal,td] at *
    nlinarith
  have hbase : 0 < transitionDiagonalF td := by
    rw [he]
    exact transitionF_pos ⟨by linarith [td_bounds.1],le_rfl⟩
  exact hbase.trans_le (hmono ⟨le_rfl,td_bounds.2.le⟩ ht ht.1)

lemma transition_actual_pos {a u : ℝ} (h : Admissible a u)
    (hT : label a u=side a u) (ht : 2/5 ≤ label a u) :
    0 < 1/2-u-(a0-1/2)*Real.sin (gap-label a u+s0)+Y0*Real.cos (gap-label a u+s0) := by
  have htop := (side_segment h hT).2.1
  by_cases hc : label a u ≤ td
  · have hp := transitionF_pos ⟨ht,hc⟩
    simp only [sideTopU,ite_eq_left hc] at htop
    dsimp [transitionF,transitionAngle,sideU] at hp htop
    linarith
  · have hp := transitionDiagonalF_pos ⟨(lt_of_not_ge hc).le,h.label_le_quarter⟩
    simp only [sideTopU,ite_eq_right hc] at htop
    dsimp [transitionDiagonalF,transitionAngle] at hp
    linarith

def diagonalK (t : ℝ) : ℝ :=
  (6/5)*(Real.pi/6-t)+(51/40)*Real.cos (7*Real.pi/12-t)-
    (11/40)*Real.sin (7*Real.pi/12-t)

private def diagonalSlope (x : ℝ) : ℝ := (51/40)*Real.sin x+(11/40)*Real.cos x

lemma diagonalSlope_gt {x : ℝ}
    (hx : Real.pi/3 ≤ x ∧ x ≤ 7*Real.pi/12-2/5) : (6:ℝ)/5 < diagonalSlope x := by
  let f : ℝ → ℝ := fun y => diagonalSlope y-6/5
  let df : ℝ → ℝ := fun y => (51/40)*Real.cos y-(11/40)*Real.sin y
  let dd : ℝ → ℝ := fun y => -diagonalSlope y
  have d1 (y : ℝ) : HasDerivAt f (df y) y := by
    convert (((Real.hasDerivAt_sin y).const_mul (51/40)).add
      ((Real.hasDerivAt_cos y).const_mul (11/40))).sub_const (6/5) using 1
    · rfl
    · dsimp [df]; ring
  have d2 (y : ℝ) : HasDerivAt df (dd y) y := by
    convert (((Real.hasDerivAt_cos y).const_mul (51/40)).sub
      ((Real.hasDerivAt_sin y).const_mul (11/40))) using 1
    dsimp [dd,diagonalSlope]; ring
  have dsign (y : ℝ) (hy : y ∈ Icc (Real.pi/3) (7*Real.pi/12-2/5)) : dd y ≤ 0 := by
    have hy0 : 0 ≤ y := by linarith [hy.1,Real.pi_pos]
    have hyp : y ≤ Real.pi/2 := by linarith [hy.2,pi_upper_22]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hy0 (by linarith [hyp,Real.pi_pos])
    have hc := cos_nonneg_quarter ⟨by linarith [hy0,Real.pi_pos],hyp⟩
    dsimp [dd,diagonalSlope]
    linarith
  have hl : 0 < f (Real.pi/3) := by
    dsimp [f,diagonalSlope]
    rw [Real.sin_pi_div_three,Real.cos_pi_div_three]
    linarith [sqrt_three_bounds.1]
  have hu : 0 < f (7*Real.pi/12-2/5) := by
    let z := 7*Real.pi/12-2/5
    have hz : 7/5 < z ∧ z < Real.pi/2 := by dsimp [z]; constructor <;> linarith [pi_lower_157,pi_upper_22]
    have hs := sin_le_sin_half (x := 7/5) (y := z)
      (by constructor <;> linarith [pi_lower_157])
      (by constructor <;> linarith [hz.1,hz.2,Real.pi_pos]) hz.1.le
    have hlow := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 7/5 by norm_num)
    have hc := cos_nonneg_quarter ⟨by linarith [hz.1,Real.pi_pos],hz.2.le⟩
    change 0 < diagonalSlope z-6/5
    dsimp [diagonalSlope]
    linarith
  have hp := positive_of_second_nonpos hx (by dsimp [f,diagonalSlope]; fun_prop)
    (by dsimp [df]; fun_prop) (fun y _ => d1 y) (fun y _ => d2 y) dsign hl hu
  dsimp [f] at hp
  linarith

lemma diagonalK_pos {t : ℝ} (ht : 2/5 ≤ t ∧ t ≤ Real.pi/4) : 0 < diagonalK t := by
  have hm : MonotoneOn diagonalK (Icc (2/5) (Real.pi/4)) := by
    apply monoOn_of_hasDeriv_nonneg
    · unfold diagonalK; fun_prop
    · intro x hx
      have ha : HasDerivAt (fun y : ℝ => 7*Real.pi/12-y) (-1) x := by
        convert (hasDerivAt_const x (7*Real.pi/12)).sub (hasDerivAt_id x) using 1
        · rfl
        · ring
      convert (((((hasDerivAt_const x (Real.pi/6)).sub (hasDerivAt_id x)).const_mul (6/5)).add
        (ha.cos.const_mul (51/40))).sub (ha.sin.const_mul (11/40))) using 1
      rfl
    · intro x hx
      have hh := diagonalSlope_gt
        (x := 7*Real.pi/12-x) ⟨by linarith [hx.2],by linarith [hx.1]⟩
      dsimp [diagonalSlope] at hh
      linarith
  have hbase : 0 < diagonalK (2/5) := by
    let e := 2/5-Real.pi/12
    have he : 27/200 < e ∧ e < 3/20 := by dsimp [e]; constructor <;> linarith [pi_lower_157,pi_upper_22]
    have hs := Real.sin_ge_sub_cube (show 0 ≤ e by linarith)
    have he3 : e^3 ≤ (3/20:ℝ)^3 := pow_le_pow_left₀ (by linarith [he.1]) he.2.le 3
    have heL : 29/210 ≤ e := by dsimp [e]; linarith [pi_upper_22]
    have hsL : 27/200 < Real.sin e := by nlinarith
    have hid : Real.cos (7*Real.pi/12-2/5)=Real.sin e := by
      rw [show 7*Real.pi/12-2/5=Real.pi/2-e by dsimp [e]; ring,
        Real.cos_pi_div_two_sub]
    dsimp [diagonalK]
    rw [hid]
    linarith [Real.sin_le_one (7*Real.pi/12-2/5),pi_lower_157]
  exact hbase.trans_le (hm ⟨le_rfl,by linarith [pi_lower_157]⟩ ht ht.1)

end Boundary
end SquaresInCircles.Seven
