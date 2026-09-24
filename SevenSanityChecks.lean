import SquaresInCircles.Seven

/-! Unexecuted regression statements for the completed source draft. -/
noncomputable section
open SquaresInCircles SquaresInCircles.Seven

example : Seven.radius^2=(13:ℝ)/4 := Seven.radius_sq
example : Packing Seven.model (0,0) Seven.radius := Seven.model_packing
example (c : Seven.Column) : Packing (Seven.slidingModel c) (0,0) Seven.radius :=
  Seven.sliding_packing c
example (c : Seven.Column) : ∑i,c.slots i=2*Real.sqrt 3-3 := c.sum_slots
example : Seven.Admissible 1 (1/2) := by norm_num [Seven.Admissible,phi,Seven.targetSq]
example : Seven.side 1 (1/2)=Real.pi/6 := by unfold Seven.side; ring
example (a u : ℝ) : Seven.remainder a u=
    (a-1)^2+(u-1/2)^2+Seven.targetSq-phi a u := Seven.remainder_identity a u
example : (0:ℝ)<Seven.axialPairPolynomial (11/10) :=
  Seven.axialPairPolynomial_pos (by norm_num)
example : (0:ℝ)<Seven.axialRatioPolynomial (7/4) :=
  Seven.axialRatioPolynomial_pos (by norm_num)
example : (0:ℝ)<Seven.radialPolynomial (5/8) :=
  Seven.radialPolynomial_pos (by norm_num)
example (v : ℝ) : (0:ℝ)<Seven.radialE (5/8) v :=
  Seven.radialE_pos (by norm_num) v
example : Seven.radialPolynomial (5/8)=
    (125352005285647:ℝ)/418089296461824000 := by
  norm_num [Seven.radialPolynomial]

example : Seven.MarkerArcStatement := Seven.markerArc_proved
example : Seven.FixedGapStatement := Seven.fixedGap_proved
example : Seven.GeometricReductionStatement := Seven.geometricReduction_proved
example : Seven.MarkerSeparationStatement := Seven.marker_separation

example {a u A v g : ℝ} (s t : Seven.TransverseSign) (k : Fin 4)
    (h : Seven.StrictlyAdmissible a u) (h' : Seven.StrictlyAdmissible A v)
    (hg : 0≤g ∧ g≤Real.pi/3) : 0<Seven.pairSupport a u A v s t k g :=
  Seven.all_gap_support_pos s t k h h' hg

example (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hext : ∀i,¬openSquare (S i) o) :
    (13:ℝ)/4≤R^2 := Seven.six_exterior_squared_lower S o R hp hext

example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (13:ℝ)/4≤R^2 := Seven.squared_lower S o R hp

example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Seven.radius≤R := Seven.optimality S o R hp

example (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Real.sqrt 13/2≤R := Seven.optimality_sqrt_thirteen_half S o R hp

example :
    (∀(S : Fin 7 → UnitSquare)(o : Point)(R : ℝ),Packing S o R → Seven.radius≤R) ∧
    ∃(S : Fin 7 → UnitSquare)(o : Point),Packing S o Seven.radius :=
  Seven.optimality_and_attainment
