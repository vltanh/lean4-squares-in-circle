import SquaresInCircles

/-!
Regression checks: the radius and centre tables, the exact rational margins the
proofs rely on, the contact points of the polygon relaxations, the public
statements, and the sliding packings of seven squares.
-/
noncomputable section
open SquaresInCircles

-- The radius table.
example : optimalRadius 1 = Real.sqrt 2 / 2 := rfl
example : optimalRadius 2 = Real.sqrt 5 / 2 := rfl
example : optimalRadius 3 = 5 * Real.sqrt 17 / 16 := rfl
example : optimalRadius 4 = Real.sqrt 2 := rfl
example : optimalRadius 5 = Real.sqrt (5 / 2) := rfl
example : optimalRadius 7 = Real.sqrt 13 / 2 := rfl

-- The centre table.
example : modelCenters 1 = ![(0,0)] := rfl
example : modelCenters 2 = ![(-1/2,0),(1/2,0)] := rfl
example : modelCenters 3 = ![(-1/2,-5/16),(1/2,-5/16),(0,11/16)] := rfl
example : modelCenters 4 = ![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)] := rfl
example : modelCenters 5 = ![(0,0),(1,0),(0,1),(-1,0),(0,-1)] := rfl
example : modelCenters 7 = ![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2),(0,-1),(0,0),(0,1)] :=
  rfl

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
example : (2:ℝ)/3 < Real.sqrt 2/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg 2]
example : ((5:ℝ)/6+1/2)^2+(1/2)^2 > 2 := by norm_num

-- Seven squares: the outer corners, the side state and its label, and the
-- margin of the marker arc at the near edge.
example : (3/2:ℝ)^2+1 = 13/4 := by norm_num
example : (1/2:ℝ)^2+3 = 13/4 := by norm_num
example : Seven.Admissible 1 (1/2) := by norm_num [Seven.Admissible,phi,Seven.targetSq]
example : Seven.label 1 (1/2) = Real.pi/6 := by
  have hs : Seven.side 1 (1/2) = Real.pi/6 := by unfold Seven.side; ring
  unfold Seven.label Seven.axial
  rw [hs,min_eq_right (show Real.pi/6 ≤ 5*(1/2)/4 by linarith [Real.pi_lt_d4]),
    min_eq_left (show Real.pi/6 ≤ Real.pi/4 by linarith [Real.pi_pos])]
example : (87061:ℝ) < (2951/10)^2 := by norm_num
example : ((2951:ℝ)/10-86)/384+801/1600 < 157/150 := by norm_num
example : (0:ℝ) < Seven.radialPolynomial (5/8) := Seven.radialPolynomial_pos (by norm_num)

-- Contact points of the polygon relaxations.
example : P3 (1/2) (5/16) := by norm_num [P3]
example : P3 (11/16) 0 := by norm_num [P3]
example : P4 (1/2) (1/2) := by norm_num [P4]
example : P5 1 0 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  exact ⟨by norm_num [P8],by nlinarith [Real.sqrt_nonneg 5]⟩
example : P5 ((Real.sqrt 5-1)/2) ((Real.sqrt 5-1)/2) := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  refine ⟨⟨?_,?_⟩,by linarith⟩ <;> nlinarith [Real.sqrt_nonneg 5]

-- Public statements.
example (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Three.radius ≤ R := Three.optimality S o R hp
example (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) : False :=
  three_polygon_strict_impossible S o hd hp
example (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5) (S : Fin n → UnitSquare) (o : Point)
    (hp : Packing S o (optimalRadius n)) : HasNormalForm S o (modelCenters n) :=
  uniqueness n hn S o hp
example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius 7 ≤ R := optimality 7 (Or.inr rfl) S o R hp
example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Seven.radius ≤ R := Seven.optimality S o R hp

-- The attaining packings, each in its own normal form.
example : HasNormalForm One.model (0,0) One.centers :=
  One.uniqueness One.model (0,0) One.model_packing
example : HasNormalForm Two.model (0,0) Two.centers :=
  Two.uniqueness Two.model (0,0) Two.model_packing
example : HasNormalForm Three.model (0,0) Three.centers :=
  Three.uniqueness Three.model (0,0) Three.model_packing
example : HasNormalForm Four.model (0,0) Four.centers :=
  Four.uniqueness Four.model (0,0) Four.model_packing
example : HasNormalForm Five.model (0,0) Five.centers :=
  Five.uniqueness Five.model (0,0) Five.model_packing

-- Seven squares: every position of the middle column is optimal, for example
-- the column pushed down by one fifth.
example : Packing Seven.model (0,0) Seven.radius := Seven.model_packing
example (c : Seven.Column) : Packing (Seven.slidingModel c) (0,0) Seven.radius :=
  Seven.sliding_packing c
example : ∃ c : Seven.Column, c.bottom = -6/5 ∧
    Packing (Seven.slidingModel c) (0,0) Seven.radius := by
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hl : (6/5:ℝ) ≤ Seven.columnLimit := by
    unfold Seven.columnLimit
    nlinarith [Real.sqrt_nonneg (3:ℝ)]
  exact ⟨⟨-6/5,-1/5,4/5,by linarith,by norm_num,by norm_num,by linarith⟩,rfl,
    Seven.sliding_packing _⟩
