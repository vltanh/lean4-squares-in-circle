import ThreeUnitSquaresInCircle

/-!
Dependency audit. Every line below must report exactly
`[propext, Classical.choice, Quot.sound]`.

Any appearance of `sorryAx` would mean an unproved lemma; any appearance of
`Lean.ofReduceBool` would mean `native_decide` and compiler trust. Neither is
used in this development.
-/

-- The unrestricted results.
#print axioms ThreeUnitSquaresInCircle.Cert.optimality
#print axioms ThreeUnitSquaresInCircle.Cert.optimality_and_attainment

-- The geometric and analytic reductions.
#print axioms ThreeUnitSquaresInCircle.Cert.normalize_orientations
#print axioms ThreeUnitSquaresInCircle.Cert.choose_separating_axes
#print axioms ThreeUnitSquaresInCircle.Cert.forbidden_chain
#print axioms ThreeUnitSquaresInCircle.Cert.polynomial_concave
#print axioms ThreeUnitSquaresInCircle.Cert.coefficient_identity

-- Supporting layers.
#print axioms ThreeUnitSquaresInCircle.Cert.select_certificate
#print axioms ThreeUnitSquaresInCircle.Cert.table_dual_bound
#print axioms ThreeUnitSquaresInCircle.Cert.table_checked
#print axioms ThreeUnitSquaresInCircle.Cert.checked_corner_lower
#print axioms ThreeUnitSquaresInCircle.Cert.certificate_on_hull
#print axioms ThreeUnitSquaresInCircle.Combinatorics.classification
#print axioms ThreeUnitSquaresInCircle.exists_packing_at_optimum
#print axioms ThreeUnitSquaresInCircle.three_square_dual

-- The statements being proved, for inspection.
#print ThreeUnitSquaresInCircle.Packing
#check @ThreeUnitSquaresInCircle.Cert.optimality
#check @ThreeUnitSquaresInCircle.Cert.optimality_and_attainment
