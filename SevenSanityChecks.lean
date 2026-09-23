import SquaresInCircles.Seven

noncomputable section
open SquaresInCircles SquaresInCircles.Seven

example : Seven.radius^2 = (13 : ℝ)/4 := Seven.radius_sq
example : Packing Seven.model (0,0) Seven.radius := Seven.model_packing
example (c : Seven.Column) : Packing (Seven.slidingModel c) (0,0) Seven.radius :=
  Seven.sliding_packing c
example (c : Seven.Column) : ∑ i, c.slots i = 2*Real.sqrt 3-3 := c.sum_slots
example : Seven.Admissible 1 (1/2) := by norm_num [Seven.Admissible, phi, Seven.targetSq]
example : Seven.side 1 (1/2) = Real.pi/6 := by unfold Seven.side; ring
example (a u : ℝ) : Seven.remainder a u =
    (a-1)^2+(u-1/2)^2+Seven.targetSq-phi a u := Seven.remainder_identity a u
example : (0 : ℝ) < Seven.axialPairPolynomial (11/10) :=
  Seven.axialPairPolynomial_pos (by norm_num)
example : (0 : ℝ) < Seven.axialRatioPolynomial (7/4) :=
  Seven.axialRatioPolynomial_pos (by norm_num)
example : (0 : ℝ) < Seven.radialPolynomial (5/8) :=
  Seven.radialPolynomial_pos (by norm_num)
example (v : ℝ) : (0 : ℝ) < Seven.radialE (5/8) v :=
  Seven.radialE_pos (by norm_num) v
example : Seven.radialPolynomial (5/8) =
    (125352005285647 : ℝ)/418089296461824000 := by
  norm_num [Seven.radialPolynomial]
example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    ∃ e : Fin 6 ↪ Fin 7, ∀ i, ¬ openSquare (S (e i)) o :=
  Seven.six_exterior_indices S o hp.disjoint
