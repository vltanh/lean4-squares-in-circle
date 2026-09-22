import ThreeUnitSquaresInCircle

/-!
Dependency audit. Every line below must report exactly
`[propext, Classical.choice, Quot.sound]`.

Any appearance of `sorryAx` would mean an unproved lemma; any appearance of
`Lean.ofReduceBool` would mean `native_decide` and compiler trust. Neither is
used in this development.
-/

-- The three-square result.
#print axioms ThreeUnitSquaresInCircle.ThreeArc.optimality
#print axioms ThreeUnitSquaresInCircle.ThreeArc.optimality_and_attainment

-- Four and five squares, and the combined interface.
#print axioms ThreeUnitSquaresInCircle.Unified.four_optimality
#print axioms ThreeUnitSquaresInCircle.Unified.five_optimality
#print axioms ThreeUnitSquaresInCircle.Unified.optimality_and_attainment_345

-- The strict polygon relaxations, and the two three-square alternatives.
#print axioms ThreeUnitSquaresInCircle.Unified.three_polygon_strict_impossible
#print axioms ThreeUnitSquaresInCircle.Unified.three_exterior_reduction
#print axioms ThreeUnitSquaresInCircle.Unified.three_containing_impossible
#print axioms ThreeUnitSquaresInCircle.Unified.four_polygon_strict_impossible
#print axioms ThreeUnitSquaresInCircle.Unified.five_polygon_strict_impossible

-- The shared framework.
#print axioms ThreeUnitSquaresInCircle.support_separator
#print axioms ThreeUnitSquaresInCircle.Unified.safe_openRay_of_disjoint
#print axioms ThreeUnitSquaresInCircle.Unified.open_arc_budget
#print axioms ThreeUnitSquaresInCircle.Unified.OpenArc.third_distance_bounds
#print axioms ThreeUnitSquaresInCircle.Unified.three_compensation
#print axioms ThreeUnitSquaresInCircle.Unified.near_axis_square_overlap

-- Attaining configurations.
#print axioms ThreeUnitSquaresInCircle.exists_packing_at_optimum
#print axioms ThreeUnitSquaresInCircle.Unified.block_packing
#print axioms ThreeUnitSquaresInCircle.Unified.plus_packing

-- The statements being proved, for inspection.
#print ThreeUnitSquaresInCircle.Packing
#print ThreeUnitSquaresInCircle.Unified.PackingN
#check @ThreeUnitSquaresInCircle.ThreeArc.optimality
#check @ThreeUnitSquaresInCircle.ThreeArc.optimality_and_attainment
#check @ThreeUnitSquaresInCircle.Unified.four_optimality
#check @ThreeUnitSquaresInCircle.Unified.five_optimality
#check @ThreeUnitSquaresInCircle.Unified.optimality_and_attainment_345
