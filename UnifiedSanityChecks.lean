import ThreeUnitSquaresInCircle.Unified

/-! Closed exact-arithmetic checks and regression statements.
These are Lean proof scripts, not a report that this file has been run. -/
noncomputable section
open ThreeUnitSquaresInCircle ThreeUnitSquaresInCircle.Unified

example : ((109:ℝ)/100)^3/6 < 1/4 := by norm_num
example : (5:ℝ) < (2237/1000)^2 := by norm_num
example : ((707:ℝ)/1000)^2 < 1/2 := by norm_num
example : (401:ℝ)/500 < 1-((22:ℝ)/35)^2/2 := by norm_num
example : (1:ℝ) < (401/500)^2+(3/5)^2 := by norm_num
example : (17:ℝ)/30 < (707/1000)*(401/500) := by norm_num
example : (6:ℝ)/5*(237/1000)+(54/125)*(237/1000)^3 < 313/1000 := by norm_num
example : (6:ℝ)/5*(237/1000)+(54/125)*(23/60)^3 < 313/1000 := by norm_num
example : (6:ℝ)/5*(1-2*(23/60))+(54/125)*(23/60)^3 < 313/1000 := by norm_num

example : P3 (1/2) (5/16) := by norm_num [P3]
example : P3 (11/16) 0 := by norm_num [P3]
example : P4 (1/2) (1/2) := by norm_num [P4]
example : P8 1 0 := by norm_num [P8]
example : PackingN block (0,0) (Real.sqrt 2) := block_packing
example : PackingN plus (0,0) (Real.sqrt ((5:ℝ)/2)) := plus_packing
example (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ) :
    PackingN S o R ↔ Packing S o R := Iff.rfl
