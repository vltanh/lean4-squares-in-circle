import ThreeUnitSquaresInCircle

/-!
Regression checks: the exact rational margins the proof relies on, the contact
points of the polygon relaxations, and the public statements.
-/
noncomputable section
open ThreeUnitSquaresInCircle ThreeUnitSquaresInCircle.Unified
open ThreeUnitSquaresInCircle.Uniqueness

-- Three squares: deficit, radial and transverse margins.
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

-- Four and five squares: radical and Taylor margins.
example : ((109:ℝ)/100)^3/6 < 1/4 := by norm_num
example : (5:ℝ) < (2237/1000)^2 := by norm_num
example : ((707:ℝ)/1000)^2 < 1/2 := by norm_num
example : (401:ℝ)/500 < 1-((22:ℝ)/35)^2/2 := by norm_num
example : (1:ℝ) < (401/500)^2+(3/5)^2 := by norm_num
example : (17:ℝ)/30 < (707/1000)*(401/500) := by norm_num
example : (6:ℝ)/5*(237/1000)+(54/125)*(237/1000)^3 < 313/1000 := by norm_num
example : (6:ℝ)/5*(237/1000)+(54/125)*(23/60)^3 < 313/1000 := by norm_num
example : (6:ℝ)/5*(1-2*(23/60))+(54/125)*(23/60)^3 < 313/1000 := by norm_num

-- Contact points of the polygon relaxations.
example : P3 (1/2) (5/16) := by norm_num [P3]
example : P3 (11/16) 0 := by norm_num [P3]
example : P4 (1/2) (1/2) := by norm_num [P4]
example : P8 1 0 := by norm_num [P8]

-- Public statements.
example (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ) :
    PackingN S o R ↔ Packing S o R := Iff.rfl
example (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius ≤ R := ThreeArc.optimality S o R hp
example (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) : False :=
  three_polygon_strict_impossible S o hd hp
example : PackingN block (0,0) (Real.sqrt 2) := block_packing
example : PackingN plus (0,0) (Real.sqrt ((5:ℝ)/2)) := plus_packing

-- Uniqueness: margins, and the attaining packings in their own normal forms.
example : (2:ℝ)/3 < Real.sqrt 2/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]
example : ((5:ℝ)/6+1/2)^2+(1/2)^2 > 2 := by norm_num
example : HasNormalForm tSquares tCenter threeCenters :=
  ThreeUniqueness.uniqueness tSquares tCenter tSquares_packing
example : HasNormalForm block (0,0) fourCenters :=
  FourUniqueness.uniqueness block (0,0) block_packing
example : HasNormalForm plus (0,0) fiveCenters :=
  FiveUniqueness.uniqueness plus (0,0) plus_packing
