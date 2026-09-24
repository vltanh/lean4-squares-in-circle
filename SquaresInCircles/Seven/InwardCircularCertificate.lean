import SquaresInCircles.Seven.InwardOppositeGeometry
import SquaresInCircles.Seven.PolynomialCertificates

/-!
# A two-circle certificate for the inward axis

With opposite signs, the radical envelope is bounded by an explicit quadratic,
which turns the support bound into `radialE`, positive by a Bernstein
certificate.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven
open Boundary TaylorPoly

lemma circle_quadratic_upper {v : ℝ} (hv : 0 ≤ v ∧ v ≤ 3/10) :
    circle v-1/2 ≤ Real.sqrt 3-1-(15/52)*v-(15/52+1/42)*v^2 := by
  let a : ℝ := 15/52
  let b : ℝ := 15/52+1/42
  let B := Real.sqrt 3-a*v-b*v^2
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hr : 0 ≤ 3-v-v^2 := by nlinarith [hv.1,hv.2]
  have hrad := Real.sq_sqrt hr
  have hroot := Real.sqrt_nonneg (3-v-v^2)
  have hB0 : 0 < B := by
    have hv2 : v^2 ≤ (3/10:ℝ)^2 := by nlinarith
    dsimp [B,a,b]
    nlinarith [sqrt_three_bounds.1]
  have hcoeff1 : 0 ≤ 1-2*Real.sqrt 3*a := by
    dsimp [a]
    linarith [sqrt_three_bounds.2]
  have hcoeff2 : 0 < 1-2*Real.sqrt 3*b+a^2 := by
    dsimp [a,b]
    linarith [sqrt_three_bounds.2]
  have p1 := mul_nonneg hv.1 hcoeff1
  have p2 := mul_nonneg (sq_nonneg v) hcoeff2.le
  have p3 : 0 ≤ 2*a*b*v^3 := mul_nonneg (by dsimp [a,b]; norm_num) (pow_nonneg hv.1 3)
  have p4 : 0 ≤ b^2*v^4 := by positivity
  have hid : B^2-(3-v-v^2)=v*(1-2*Real.sqrt 3*a)+
      v^2*(1-2*Real.sqrt 3*b+a^2)+2*a*b*v^3+b^2*v^4 := by
    dsimp [B]
    nlinarith
  have hle : Real.sqrt (3-v-v^2) ≤ B := by nlinarith
  have he : targetSq-(v+1/2)^2=3-v-v^2 := by dsimp [targetSq]; ring
  dsimp [circle]
  rw [he]
  dsimp [B,a,b] at hle
  linarith

lemma radial_trig_lower {z v r : ℝ}
    (hz : 0 ≤ z ∧ z ≤ 5/8) (hv : 0 ≤ v)
    (hr : 73/100 ≤ r ∧ r ≤ 733/1000) :
    radialB z+v*radialL z+v^2*radialK z ≤
      (4/5)*z-(r-(15/52)*v-(15/52+1/42)*v^2)*Real.sin z-
        (v+1/2)*(1-Real.cos z) := by
  have hsinL := Real.sin_ge_sub_cube hz.1
  have hsinU := sin_upper_five hz.1
  have hcosL := cos_lower_six hz.1
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hbase := mul_le_mul_of_nonneg_left hsinU hr0
  have h1 := mul_nonneg hz.1 (show 0 ≤ 733/1000-r by linarith [hr.2])
  have h3 := mul_nonneg (pow_nonneg hz.1 3) (show 0 ≤ r-73/100 by linarith [hr.1])
  have h5 := mul_nonneg (pow_nonneg hz.1 5) (show 0 ≤ 733/1000-r by linarith [hr.2])
  have hvSin := mul_le_mul_of_nonneg_left hsinL
    (show 0 ≤ (15/52)*v by positivity)
  have hv2Sin := mul_le_mul_of_nonneg_left hsinL
    (show 0 ≤ (15/52+1/42)*v^2 by positivity)
  have hcos := mul_le_mul_of_nonneg_left hcosL
    (show 0 ≤ v+1/2 by linarith)
  dsimp [radialB,radialL,radialK]
  nlinarith

lemma inward_circular_pos {a u A v z : ℝ}
    (h : Admissible a u) (h' : Admissible A v)
    (hT : label a u=side a u) (hA : label A v=axial v)
    (he : z=label a u+label A v-Real.pi/6)
    (hz : 0 < z ∧ z ≤ 5/8) (hv : v ≤ 3/10) :
    0 < inwardOpposite a A v z := by
  have hupper := (a_le_circle h').trans (show circle v ≤ circle v by rfl)
  have hquad := circle_quadratic_upper ⟨h'.1,hv⟩
  have hAupper : A-1/2 ≤ Real.sqrt 3-1-(15/52)*v-(15/52+1/42)*v^2 := by
    linarith
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hz.1.le
    (by linarith [hz.2,pi_lower_157])
  have hmul := mul_le_mul_of_nonneg_right hAupper hs0
  have hW := side_remainder_quadratic h hT
  have hwarg : label a u-Real.pi/6=z-(5/4)*v := by
    rw [hA] at he
    dsimp [axial] at he
    linarith
  rw [hwarg] at hW
  have htrig := radial_trig_lower ⟨hz.1.le,hz.2⟩ h'.1
    (r := Real.sqrt 3-1) ⟨by linarith [sqrt_three_bounds.1],by linarith [sqrt_three_bounds.2]⟩
  have hp := radialE_pos hz v
  rw [inward_opposite_side_identity hT hA he]
  rw [abs_of_nonneg hs0]
  dsimp [radialE] at hp
  nlinarith

lemma line_to_circle_turn_margin {z : ℝ}
    (hz : 19/100 ≤ z ∧ z ≤ Real.pi/3) :
    (12:ℝ)/13 < (44/45)*Real.sin z+(4/5)*Real.cos z := by
  let f : ℝ → ℝ := fun x => (44/45)*Real.sin x+(4/5)*Real.cos x-12/13
  let df : ℝ → ℝ := fun x => (44/45)*Real.cos x-(4/5)*Real.sin x
  let dd : ℝ → ℝ := fun x => -(44/45)*Real.sin x-(4/5)*Real.cos x
  have hd (x : ℝ) : HasDerivAt f (df x) x := by
    convert (((Real.hasDerivAt_sin x).const_mul (44/45)).add
      ((Real.hasDerivAt_cos x).const_mul (4/5))).sub_const (12/13) using 1
    dsimp [df]; ring
  have hdd (x : ℝ) : HasDerivAt df (dd x) x := by
    convert ((Real.hasDerivAt_cos x).const_mul (44/45)).sub
      ((Real.hasDerivAt_sin x).const_mul (4/5)) using 1
    dsimp [dd]; ring
  have hsign (x : ℝ) (hx : x ∈ Icc (19/100) (Real.pi/3)) : dd x ≤ 0 := by
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (x := x)
      (by linarith [hx.1]) (by linarith [hx.2,Real.pi_pos])
    have hc := cos_nonneg_quarter (x := x)
      ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_pos]⟩
    dsimp [dd]
    linarith
  have hlo : 0 < f (19/100) := by
    have hs := Real.sin_ge_sub_cube (show (0:ℝ) ≤ 19/100 by norm_num)
    have hc := Real.one_sub_sq_div_two_le_cos (x := (19/100:ℝ))
    dsimp [f]
    linarith
  have hhi : 0 < f (Real.pi/3) := by
    dsimp [f]
    rw [Real.sin_pi_div_three,Real.cos_pi_div_three]
    linarith [sqrt_three_bounds.1]
  have hp := positive_of_second_nonpos hz (by dsimp [f]; fun_prop)
    (by dsimp [df]; fun_prop) (fun x _ => hd x) (fun x _ => hdd x) hsign hlo hhi
  dsimp [f] at hp
  linarith

end SquaresInCircles.Seven
