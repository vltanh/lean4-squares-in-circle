import ThreeUnitSquaresInCircle.ThreeUniqueness
import ThreeUnitSquaresInCircle.FourUniqueness
import ThreeUnitSquaresInCircle.FiveUniqueness
import ThreeUnitSquaresInCircle.Unified.Constructions

noncomputable section
open ThreeUnitSquaresInCircle ThreeUnitSquaresInCircle.Unified
open ThreeUnitSquaresInCircle.Uniqueness

example : (2:ℝ)/3 < Real.sqrt 2/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]
example : ((5:ℝ)/6+1/2)^2+(1/2)^2 > 2 := by norm_num
example : (46:ℝ)/609 < 1/12 := by norm_num
example : (9:ℝ)/20 < 1/2 := by norm_num
example : P3 (1/2) (5/16) := by norm_num [P3]
example : P3 (11/16) 0 := by norm_num [P3]
example : HasNormalForm tSquares tCenter threeCenters :=
  ThreeUniqueness.uniqueness tSquares tCenter tSquares_packing
example : HasNormalForm block (0,0) fourCenters :=
  FourUniqueness.uniqueness block (0,0) block_packing
example : HasNormalForm plus (0,0) fiveCenters :=
  FiveUniqueness.uniqueness plus (0,0) plus_packing
