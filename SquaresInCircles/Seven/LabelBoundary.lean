import SquaresInCircles.Seven.SectorBounds

/-!
# Exact label-boundary geometry

The transition constants are radicals in pi. The side-circle parametrization
uses the two perpendicular coefficient vectors (3/4,-1/3) and (1/3,3/4).
Its square-root denominator is exactly the derivative denominator L from the
manuscript. This avoids introducing an additional polar-angle parameter.

Incremental, uncompiled proof draft.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace Boundary

def M : ℝ := 2*Real.pi+17
def J : ℝ := Real.sqrt (202*targetSq-M^2)
def X0 : ℝ := (9*M+11*J)/202
def Y0 : ℝ := (11*M-9*J)/202
def a0 : ℝ := X0-1/2
def u0 : ℝ := Y0-1/2
def s0 : ℝ := (5/4)*u0
def rd : ℝ := Real.sqrt (13/8)-1/2
def td : ℝ := Real.pi/6+7/12-(5/12)*rd

def N : ℝ := 97/144
def D (t : ℝ) : ℝ := Real.pi/6+19/24-t
def Z (t : ℝ) : ℝ := Real.sqrt (N*targetSq-(D t)^2)
def X (t : ℝ) : ℝ := ((3/4)*D t+Z t/3)/N
def Y (t : ℝ) : ℝ := (-D t/3+(3/4)*Z t)/N
def sideA (t : ℝ) : ℝ := X t-1/2
def sideU (t : ℝ) : ℝ := Y t-1/2

def circle (u : ℝ) : ℝ := Real.sqrt (targetSq-(u+1/2)^2)-1/2
def axialLine (u : ℝ) : ℝ := (2*Real.pi+7-11*u)/9
def axialTop (u : ℝ) : ℝ := min (circle u) (axialLine u)
def tieA (t : ℝ) : ℝ := (2*Real.pi+7)/9-(44/45)*t
def diagonal (t : ℝ) : ℝ := (2*Real.pi+7-12*t)/5

def sideTopU (t : ℝ) : ℝ := if t ≤ td then sideU t else diagonal t
def sideTopA (t : ℝ) : ℝ := if t ≤ td then sideA t else diagonal t

lemma pi_bounds : (3141592:ℝ)/1000000 < Real.pi ∧ Real.pi < 3141593/1000000 := by
  constructor
  · linarith [Real.pi_gt_d6]
  · linarith [Real.pi_lt_d6]

lemma J_sq : J^2=202*targetSq-M^2 := by
  apply Real.sq_sqrt
  have hp := pi_bounds
  dsimp [M,targetSq]
  nlinarith

lemma J_bounds : (1069547:ℝ)/100000 < J ∧ J < 1069549/100000 := by
  have hp := pi_bounds
  have hsq := J_sq
  have hn : 0 ≤ J := Real.sqrt_nonneg _
  dsimp [M,targetSq] at hsq
  constructor <;> nlinarith

lemma transition_bounds :
    (111979:ℝ)/100000 < a0 ∧ a0 < 111980/100000 ∧
    (29136:ℝ)/100000 < u0 ∧ u0 < 29137/100000 := by
  have hp := pi_bounds
  have hj := J_bounds
  dsimp [a0,u0,X0,Y0,M]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma transition_coarse :
    (11:ℝ)/10 < a0 ∧ a0 < 9/8 ∧
    (29:ℝ)/100 < u0 ∧ u0 < 3/10 ∧
    (9:ℝ)/25 < s0 ∧ s0 < 2/5 := by
  have h := transition_bounds
  dsimp [s0]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma transition_circle : X0^2+Y0^2=targetSq := by
  have hj := J_sq
  dsimp [X0,Y0]
  nlinarith

lemma transition_line : 9*a0+11*u0=2*Real.pi+7 := by
  dsimp [a0,u0,X0,Y0,M]
  ring

lemma transition_admissible : Admissible a0 u0 := by
  have hc := transition_coarse
  have he := transition_circle
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  dsimp [phi,a0,u0]
  nlinarith

lemma transition_labels : label a0 u0=axial u0 ∧ label a0 u0=side a0 u0 := by
  have hl := transition_line
  have hc := transition_coarse
  have he : axial u0=side a0 u0 := by dsimp [axial,side]; linarith
  have hcap : axial u0 ≤ Real.pi/4 := by
    dsimp [axial]
    linarith [pi_lower_157]
  simp [label,he,show side a0 u0 ≤ Real.pi/4 by simpa only [← he] using hcap]

lemma rd_bounds : (77475:ℝ)/100000 < rd ∧ rd < 77476/100000 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 13/8 by norm_num)
  have hn := Real.sqrt_nonneg (13/8:ℝ)
  dsimp [rd]
  constructor <;> nlinarith

lemma td_bounds : (18:ℝ)/25 < td ∧ td < Real.pi/4 := by
  have hp := pi_bounds
  have hr := rd_bounds
  dsimp [td]
  constructor <;> linarith

lemma D_td : D td=(5/12)*(rd+1/2) := by
  dsimp [D,td]
  ring

lemma D_s0 : D s0=(3/4)*X0-Y0/3 := by
  have hl := transition_line
  dsimp [D,s0,a0,u0] at *
  linarith

lemma D_range {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    (1:ℝ)/2 < D t ∧ D t < 1 := by
  have hr := rd_bounds
  have hs := transition_coarse
  have hp := pi_bounds
  dsimp [D,td] at *
  dsimp [s0] at ht
  constructor <;> linarith

lemma radicand_pos {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    0 < N*targetSq-(D t)^2 := by
  have h := D_range ht
  dsimp [N,targetSq]
  nlinarith

lemma Z_pos {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) : 0 < Z t :=
  Real.sqrt_pos.mpr (radicand_pos ht)

lemma Z_sq {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    (Z t)^2=N*targetSq-(D t)^2 :=
  Real.sq_sqrt (radicand_pos ht).le

lemma circle_identities {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    (X t)^2+(Y t)^2=targetSq ∧
    (3/4)*X t-Y t/3=D t ∧ X t/3+(3/4)*Y t=Z t := by
  have hz := Z_sq ht
  constructor
  · dsimp [X,Y,N] at *
    nlinarith
  constructor <;> dsimp [X,Y,N] <;> ring

lemma circle_label {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    side (sideA t) (sideU t)=t := by
  have hl := (circle_identities ht).2.1
  dsimp [side,sideA,sideU,D] at *
  linarith

lemma side_at_transition : sideA s0=a0 ∧ sideU s0=u0 := by
  have hc := transition_circle
  have hl := D_s0
  have hp := transition_coarse
  have ht : s0 ≤ s0 ∧ s0 ≤ td := by
    exact ⟨le_rfl,by linarith [td_bounds.1]⟩
  have hz := Z_sq ht
  have hz0 := Z_pos ht
  have hid : Z s0=X0/3+(3/4)*Y0 := by
    have hn : 0 < X0/3+(3/4)*Y0 := by
      dsimp [a0,u0] at hp
      linarith
    rw [hl] at hz
    dsimp [N] at hz
    nlinarith
  dsimp [sideA,sideU,X,Y,a0,u0,N]
  rw [hl,hid]
  constructor <;> ring

lemma side_at_diagonal : sideA td=rd ∧ sideU td=rd := by
  have hr := rd_bounds
  have hs : (rd+1/2)^2=targetSq/2 := by
    dsimp [rd,targetSq]
    simpa using Real.sq_sqrt (show (0:ℝ) ≤ 13/8 by norm_num)
  have ht : s0 ≤ td ∧ td ≤ td := ⟨by linarith [transition_coarse.2.2.2.2.2,td_bounds.1],le_rfl⟩
  have hz := Z_sq ht
  have hp := Z_pos ht
  rw [D_td] at hz
  have he : Z td=(13/12)*(rd+1/2) := by
    dsimp [N] at hz
    nlinarith
  dsimp [sideA,sideU,X,Y,N]
  rw [D_td,he]
  constructor <;> ring

lemma circle_bounds {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    0 < Y t ∧ Y0 ≤ Y t ∧ Y t ≤ X t ∧
    (5:ℝ)/4 < X t ∧ X t ≤ X0 ∧
    1 < Z t ∧ Z t < 7/5 := by
  have hd := D_range ht
  have hz := Z_sq ht
  have hz0 := Z_pos ht
  have hc := circle_identities ht
  have h0 := transition_coarse
  have hr := rd_bounds
  have ht0 : s0 ≤ s0 ∧ s0 ≤ td := ⟨le_rfl,le_trans ht.1 ht.2⟩
  have hzbase := Z_sq ht0
  have hbase := side_at_transition
  have hdle : D t ≤ D s0 := by dsimp [D]; linarith [ht.1]
  have hdz : D td ≤ D t := by dsimp [D]; linarith [ht.2]
  have hzle : Z s0 ≤ Z t := by
    have hdb := D_range ht0
    have hzb := Z_pos ht0
    nlinarith
  have hY0 : Y0 ≤ Y t := by
    have hy0 : Y s0=Y0 := by
      have hh := hbase.2
      dsimp [sideU,u0] at hh
      linarith
    dsimp [Y]
    rw [← hy0]
    dsimp [Y,N]
    linarith
  have hYpos : 0 < Y t := by dsimp [u0] at h0; linarith
  have hXpos : 0 < X t := by dsimp [X,N]; positivity
  have hXY : Y t ≤ X t := by
    have hrd : (rd+1/2)^2=targetSq/2 := by
      dsimp [rd,targetSq]
      simpa using Real.sq_sqrt (show (0:ℝ) ≤ 13/8 by norm_num)
    rw [D_td] at hdz
    have hprod := mul_nonneg (sub_nonneg.mpr hdz)
      (show 0 ≤ D t+(5/12)*(rd+1/2) by linarith)
    have hcomp : 5*Z t ≤ 13*D t := by
      dsimp [N] at hz
      nlinarith
    dsimp [X,Y,N]
    linarith
  have hXlower : (5:ℝ)/4 < X t := by
    have hYY := mul_nonneg (sub_nonneg.mpr hXY) (add_nonneg hXpos.le hYpos.le)
    dsimp [targetSq] at hc
    nlinarith
  have hXupper : X t ≤ X0 := by
    have hp := transition_circle
    have hprod := mul_nonneg (sub_nonneg.mpr hY0)
      (show 0 ≤ Y t+Y0 by dsimp [u0] at h0; linarith)
    have hX00 : 0 < X0 := by dsimp [a0] at h0; linarith
    nlinarith
  have hZlower : 1 < Z t := by
    have hb : (79:ℝ)/100 < Y0 := by dsimp [u0] at h0; linarith
    linarith [hc.2.2]
  have hsum : X t+Y t < 51/20 := by
    have hh := sq_nonneg (X t-Y t)
    dsimp [targetSq] at hc
    nlinarith
  have hZupper : Z t < 7/5 := by linarith [hc.2.2]
  exact ⟨hYpos,hY0,hXY,hXlower,hXupper,hZlower,hZupper⟩

lemma hasDerivAt_D (t : ℝ) : HasDerivAt D (-1) t := by
  convert (hasDerivAt_const t (Real.pi/6+19/24)).sub (hasDerivAt_id t) using 1 <;>
    simp [D]

lemma hasDerivAt_Z {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt Z (D t/Z t) t := by
  have hp := radicand_pos ht
  have hd := (hasDerivAt_const t (N*targetSq)).sub ((hasDerivAt_D t).pow 2)
  have hs := hd.sqrt (ne_of_gt hp)
  convert hs using 1
  · rfl
  · dsimp [Z]
    field_simp
    ring

lemma hasDerivAt_X {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt X (-Y t/Z t) t := by
  have hd := (((hasDerivAt_D t).const_mul (3/4)).add
    ((hasDerivAt_Z ht).div_const 3)).div_const N
  convert hd using 1
  · rfl
  · dsimp [Y]
    field_simp
    ring

lemma hasDerivAt_Y {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt Y (X t/Z t) t := by
  have hd := (((hasDerivAt_D t).div_const 3).neg.add
    ((hasDerivAt_Z ht).const_mul (3/4))).div_const N
  convert hd using 1
  · rfl
  · dsimp [X]
    field_simp
    ring

lemma hasDerivAt_Y_prime {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt (fun x => X x/Z x) (-(3/4)*targetSq/(Z t)^3) t := by
  have hz0 : Z t ≠ 0 := ne_of_gt (Z_pos ht)
  have hd := (hasDerivAt_X ht).div (hasDerivAt_Z ht) hz0
  have hc := circle_identities ht
  have hid : Y t*Z t+X t*D t=(3/4)*targetSq := by
    nlinarith [hc.1,hc.2.1,hc.2.2]
  convert hd using 1
  field_simp [hz0]
  nlinarith

lemma hasDerivAt_X_prime {t : ℝ} (ht : s0 ≤ t ∧ t ≤ td) :
    HasDerivAt (fun x => -Y x/Z x) (-(1/3)*targetSq/(Z t)^3) t := by
  have hz0 : Z t ≠ 0 := ne_of_gt (Z_pos ht)
  have hd := (hasDerivAt_Y ht).neg.div (hasDerivAt_Z ht) hz0
  have hc := circle_identities ht
  have hid : X t*Z t-Y t*D t=(1/3)*targetSq := by
    nlinarith [hc.1,hc.2.1,hc.2.2]
  convert hd using 1
  field_simp [hz0]
  nlinarith

end Boundary
end SquaresInCircles.Seven
