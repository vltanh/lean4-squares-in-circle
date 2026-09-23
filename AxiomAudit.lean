import SquaresInCircles

/-!
Dependency audit. Every line below must report exactly
`[propext, Classical.choice, Quot.sound]`.

Any appearance of `sorryAx` would mean an unproved lemma; any appearance of
`Lean.ofReduceBool` would mean `native_decide` and compiler trust. Neither is
used in this development.
-/

-- All five cases in one statement.
#print axioms SquaresInCircles.optimality
#print axioms SquaresInCircles.attainment
#print axioms SquaresInCircles.uniqueness
#print axioms SquaresInCircles.optimality_attainment_uniqueness

-- Each case: lower bound with attainment, and rigid uniqueness.
#print axioms SquaresInCircles.One.optimality_and_attainment
#print axioms SquaresInCircles.One.rigid_uniqueness
#print axioms SquaresInCircles.Two.optimality_and_attainment
#print axioms SquaresInCircles.Two.rigid_uniqueness
#print axioms SquaresInCircles.Three.optimality_and_attainment
#print axioms SquaresInCircles.Three.rigid_uniqueness
#print axioms SquaresInCircles.Four.optimality_and_attainment
#print axioms SquaresInCircles.Four.rigid_uniqueness
#print axioms SquaresInCircles.Five.optimality_and_attainment
#print axioms SquaresInCircles.Five.rigid_uniqueness
#print axioms SquaresInCircles.Five.polygon_uniqueness

-- The strict polygon relaxations, and the two three-square alternatives.
#print axioms SquaresInCircles.three_polygon_strict_impossible
#print axioms SquaresInCircles.three_exterior_reduction
#print axioms SquaresInCircles.three_containing_impossible
#print axioms SquaresInCircles.four_polygon_strict_impossible
#print axioms SquaresInCircles.five_polygon_strict_impossible

-- The shared framework.
#print axioms SquaresInCircles.support_separator
#print axioms SquaresInCircles.safe_openRay_of_disjoint
#print axioms SquaresInCircles.open_arc_budget
#print axioms SquaresInCircles.OpenArc.third_distance_bounds
#print axioms SquaresInCircles.centers_distance_sq_ge_one
#print axioms SquaresInCircles.unit_contact
#print axioms SquaresInCircles.three_compensation
#print axioms SquaresInCircles.near_axis_square_overlap

-- The statements being proved, for inspection.
#print SquaresInCircles.Packing
#print SquaresInCircles.optimalRadius
#print SquaresInCircles.HasNormalForm
#print SquaresInCircles.modelCenters
#check @SquaresInCircles.optimality
#check @SquaresInCircles.attainment
#check @SquaresInCircles.uniqueness
#check @SquaresInCircles.Five.polygon_uniqueness
