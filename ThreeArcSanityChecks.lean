import ThreeUnitSquaresInCircle.ThreeArc

/- Exact proof scripts for numerical margins. This file has not been run. -/
noncomputable section
open ThreeUnitSquaresInCircle ThreeUnitSquaresInCircle.Unified

example : (22:ℝ)/42-13/29 = 46/609 := by norm_num
example : (46:ℝ)/609 < 1/12 := by norm_num
example : (1/2:ℝ)-1/24-(1/24)^2/4 > 9/20 := by norm_num
example : (9/20:ℝ)*(3/8)=27/160 := by norm_num
example : (57/128:ℝ)-(19/8)*(27/160)=57/1280 := by norm_num
example : (57/1280:ℝ) < 1/16 := by norm_num
example : (3/5:ℝ)/5-(4/5)*(2/5)+11/16 < 1/2 := by norm_num
example : (7/8:ℝ)/5+(3/5)*(2/5)+1/16 < 1/2 := by norm_num
example : (1/5:ℝ)-11/16 > -1/2 := by norm_num
example : (2/5:ℝ)+1/16 < 1/2 := by norm_num

example (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius ≤ R := ThreeArc.optimality S o R hp

example (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) : False :=
  three_polygon_strict_impossible S o hd hp
