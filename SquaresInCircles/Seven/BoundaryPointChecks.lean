import SquaresInCircles.Seven.BoundarySegments
import SquaresInCircles.Seven.TaylorBounds

/-!
# Two fixed-point estimates

Values and slopes of the boundary profiles at two fixed angles, from rational
brackets of `π` and of the transition constants, and from Taylor bounds of
`sin` and `cos` up to degree 11.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
namespace PointTaylor

def c8 (x : ℝ) : ℝ := 1-x^2/2+x^4/24-x^6/720+x^8/40320
def s9 (x : ℝ) : ℝ := x-x^3/6+x^5/120-x^7/5040+x^9/362880
def c10 (x : ℝ) : ℝ := c8 x-x^10/3628800
def s11 (x : ℝ) : ℝ := s9 x-x^11/39916800

lemma cos_le_c8 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ c8 x := by
  let f : ℝ → ℝ := fun y => c8 y-Real.cos y
  have hd (y : ℝ) : deriv f y = Real.sin y-(y-y^3/6+y^5/120-y^7/5040) := by
    simp (disch := fun_prop) [f,c8]
    ring
  have hh := nonneg_of_deriv_nonneg f (by dsimp [f,c8]; fun_prop)
    (by norm_num [f,c8]) (fun y hy => by rw [hd]; linarith [sin_lower_seven hy]) hx
  dsimp [f] at hh
  linarith

lemma sin_le_s9 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ s9 x := by
  let f : ℝ → ℝ := fun y => s9 y-Real.sin y
  have hd (y : ℝ) : deriv f y = c8 y-Real.cos y := by
    simp (disch := fun_prop) [f,s9,c8]
    ring
  have hh := nonneg_of_deriv_nonneg f (by dsimp [f,s9]; fun_prop)
    (by norm_num [f,s9]) (fun y hy => by rw [hd]; linarith [cos_le_c8 hy]) hx
  dsimp [f] at hh
  linarith

lemma c10_le_cos {x : ℝ} (hx : 0 ≤ x) : c10 x ≤ Real.cos x := by
  let f : ℝ → ℝ := fun y => Real.cos y-c10 y
  have hd (y : ℝ) : deriv f y = s9 y-Real.sin y := by
    simp (disch := fun_prop) [f,c10,c8,s9]
    ring
  have hh := nonneg_of_deriv_nonneg f (by dsimp [f,c10,c8]; fun_prop)
    (by norm_num [f,c10,c8]) (fun y hy => by rw [hd]; linarith [sin_le_s9 hy]) hx
  dsimp [f] at hh
  linarith

lemma s11_le_sin {x : ℝ} (hx : 0 ≤ x) : s11 x ≤ Real.sin x := by
  let f : ℝ → ℝ := fun y => Real.sin y-s11 y
  have hd (y : ℝ) : deriv f y = Real.cos y-c10 y := by
    simp (disch := fun_prop) [f,s11,s9,c10,c8]
    ring
  have hh := nonneg_of_deriv_nonneg f (by dsimp [f,s11,s9]; fun_prop)
    (by norm_num [f,s11,s9]) (fun y hy => by rw [hd]; linarith [c10_le_cos hy]) hx
  dsimp [f] at hh
  linarith

lemma trig_bracket {l u x : ℝ} (hl : 0 ≤ l) (hu : u ≤ Real.pi/2)
    (hx : l ≤ x ∧ x ≤ u) :
    s11 l ≤ Real.sin x ∧ Real.sin x ≤ s9 u ∧
    c10 u ≤ Real.cos x ∧ Real.cos x ≤ c8 l := by
  have hx0 : 0 ≤ x := hl.trans hx.1
  have hu0 : 0 ≤ u := hx0.trans hx.2
  have sl := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
    (hx.2.trans hu) hx.1
  have su := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hu hx.2
  have cl := Real.cos_le_cos_of_nonneg_of_le_pi hl (by linarith [Real.pi_pos]) hx.1
  have cu := Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos]) hx.2
  exact ⟨(s11_le_sin hl).trans sl,su.trans (sin_le_s9 hu0),
    (c10_le_cos hu0).trans cu,cl.trans (cos_le_c8 hl)⟩
end PointTaylor

namespace Boundary

def testLabel : ℝ := 18/25
def testAngle : ℝ := gap-testLabel+s0
def testValue : ℝ := 1-Y testLabel-(a0-1/2)*Real.sin testAngle+Y0*Real.cos testAngle
def testSlope : ℝ := -X testLabel/Z testLabel+(a0-1/2)*Real.cos testAngle+Y0*Real.sin testAngle

def diagonalAngle : ℝ := td+s0-Real.pi/6
def diagonalValue : ℝ := 1/2-rd-(a0-1/2)*Real.sin diagonalAngle+Y0*Real.cos diagonalAngle

lemma test_mem : testLabel ∈ Icc s0 td := by
  have hs := transition_coarse
  have ht := td_bounds
  dsimp [testLabel]
  constructor <;> linarith

lemma test_radical_bounds :
    (13545829:ℝ)/10000000 < Z testLabel ∧ Z testLabel < 13545832/10000000 := by
  have hs := Z_sq test_mem
  have hp := Z_pos test_mem
  dsimp [D,testLabel,N,targetSq] at hs hp ⊢
  constructor <;> nlinarith [Real.pi_gt_d6,Real.pi_lt_d6]

lemma test_coordinate_bounds :
    (133307:ℝ)/100000 < X testLabel ∧ X testLabel < 133309/100000 ∧
    (121362:ℝ)/100000 < Y testLabel ∧ Y testLabel < 121365/100000 := by
  have hz := test_radical_bounds
  dsimp [X,Y,D,N,testLabel] at hz ⊢
  refine ⟨?_,?_,?_,?_⟩ <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]

lemma test_angle_bounds : (691397:ℝ)/1000000 ≤ testAngle ∧ testAngle ≤ 691411/1000000 := by
  have hu := transition_bounds
  dsimp [testAngle,gap,testLabel,s0]
  constructor <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]

lemma test_trig_bounds :
    (63761:ℝ)/100000 < Real.sin testAngle ∧ Real.sin testAngle < 63763/100000 ∧
    (77034:ℝ)/100000 < Real.cos testAngle ∧ Real.cos testAngle < 77036/100000 := by
  have h := PointTaylor.trig_bracket (l := (691397:ℝ)/1000000)
    (u := (691411:ℝ)/1000000) (by norm_num)
    (by linarith [pi_lower_157]) test_angle_bounds
  have hsl : (63761:ℝ)/100000 < PointTaylor.s11 (691397/1000000) := by
    norm_num [PointTaylor.s11,PointTaylor.s9]
  have hsu : PointTaylor.s9 (691411/1000000) < (63763:ℝ)/100000 := by
    norm_num [PointTaylor.s9]
  have hcl : (77034:ℝ)/100000 < PointTaylor.c10 (691411/1000000) := by
    norm_num [PointTaylor.c10,PointTaylor.c8]
  have hcu : PointTaylor.c8 (691397/1000000) < (77036:ℝ)/100000 := by
    norm_num [PointTaylor.c8]
  exact ⟨hsl.trans_le h.1,h.2.1.trans_lt hsu,hcl.trans_le h.2.2.1,h.2.2.2.trans_lt hcu⟩

lemma test_value_lower : (3:ℝ)/4000 < testValue := by
  have ha := transition_bounds
  have hy := test_coordinate_bounds
  have ht := test_trig_bounds
  have hup : (a0-1/2)*Real.sin testAngle < (61980:ℝ)/100000*(63763/100000) := by
    have ha0 : 0 ≤ a0-1/2 := by linarith
    gcongr <;> linarith
  have hlo : (79136:ℝ)/100000*(77034/100000) < Y0*Real.cos testAngle := by
    have hy0 : (79136:ℝ)/100000 < Y0 := by dsimp [u0] at ha; linarith
    gcongr
    linarith
  dsimp [testValue]
  linarith

lemma test_slope_bound : |testSlope| < (1:ℝ)/400 := by
  have ha := transition_bounds
  have hx := test_coordinate_bounds
  have hz := test_radical_bounds
  have ht := test_trig_bounds
  have hp1 : (61979:ℝ)/100000*(77034/100000) < (a0-1/2)*Real.cos testAngle := by
    gcongr <;> linarith
  have hp2 : (a0-1/2)*Real.cos testAngle < (61980:ℝ)/100000*(77036/100000) := by
    gcongr <;> linarith
  have hp3 : (79136:ℝ)/100000*(63761/100000) < Y0*Real.sin testAngle := by
    have hy0 : (79136:ℝ)/100000 < Y0 := by dsimp [u0] at ha; linarith
    gcongr
    linarith
  have hp4 : Y0*Real.sin testAngle < (79137:ℝ)/100000*(63763/100000) := by
    have hy0 : Y0 < (79137:ℝ)/100000 := by dsimp [u0] at ha; linarith
    have hy1 : 0 ≤ Y0 := by dsimp [u0] at ha; linarith
    gcongr <;> linarith
  have hlo : (133307:ℝ)/100000/(13545832/10000000) < X testLabel/Z testLabel := by
    apply (div_lt_div_iff₀ (by norm_num) (Z_pos test_mem)).mpr
    linarith
  have hup : X testLabel/Z testLabel < (133309:ℝ)/100000/(13545829/10000000) := by
    apply (div_lt_div_iff₀ (Z_pos test_mem) (by norm_num)).mpr
    linarith
  rw [abs_lt]
  dsimp [testSlope]
  rw [neg_div]
  constructor <;> linarith

lemma diagonal_angle_bounds :
    0 < diagonalAngle ∧ diagonalAngle < 5/8 ∧
    (624716:ℝ)/1000000 ≤ diagonalAngle ∧ diagonalAngle ≤ 624734/1000000 := by
  have hp := transition_bounds
  have hr := rd_bounds
  dsimp [diagonalAngle,td,s0]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma diagonal_value_lower : (1:ℝ)/250 < diagonalValue := by
  have hr := rd_bounds
  have ha := transition_bounds
  have harg := diagonal_angle_bounds
  have ht := PointTaylor.trig_bracket (l := (624716:ℝ)/1000000)
    (u := (624734:ℝ)/1000000) (by norm_num)
    (by linarith [pi_lower_157]) harg.2.2
  have hs : Real.sin diagonalAngle < (58489:ℝ)/100000 := by
    refine ht.2.1.trans_lt ?_
    norm_num [PointTaylor.s9]
  have hc : (81111:ℝ)/100000 < Real.cos diagonalAngle := by
    refine lt_of_lt_of_le ?_ ht.2.2.1
    norm_num [PointTaylor.c10,PointTaylor.c8]
  have hs0 : 0 ≤ Real.sin diagonalAngle := Real.sin_nonneg_of_nonneg_of_le_pi
    harg.1.le (by linarith [harg.2.1,pi_lower_157])
  have hup : (a0-1/2)*Real.sin diagonalAngle < (61980:ℝ)/100000*(58489/100000) := by
    gcongr <;> linarith
  have hlo : (79136:ℝ)/100000*(81111/100000) < Y0*Real.cos diagonalAngle := by
    have hy : (79136:ℝ)/100000 < Y0 := by dsimp [u0] at ha; linarith
    gcongr
  dsimp [diagonalValue]
  linarith

end Boundary
end SquaresInCircles.Seven
