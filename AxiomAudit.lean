import SquaresInCircles

/-!
Dependency audit. Every line below must report exactly
`[propext, Classical.choice, Quot.sound]`.

Any appearance of `sorryAx` would mean an unproved lemma; any appearance of
`Lean.ofReduceBool` would mean `native_decide` and compiler trust. Neither is
used in this development.
-/

-- All six cases in one statement, which depends on every case.
#print axioms SquaresInCircles.optimality
#print axioms SquaresInCircles.attainment
#print axioms SquaresInCircles.uniqueness
#print axioms SquaresInCircles.sliding_uniqueness
#print axioms SquaresInCircles.rigid_uniqueness
#print axioms SquaresInCircles.optimality_attainment_uniqueness

-- The contact-polygon arguments; only the four-square one uses the disk.
#print axioms SquaresInCircles.three_polygon_strict_impossible
#print axioms SquaresInCircles.four_diamond_impossible
#print axioms SquaresInCircles.five_polygon_strict_impossible
#print axioms SquaresInCircles.Five.polygon_uniqueness

-- The shared framework.
#print axioms SquaresInCircles.support_separator
#print axioms SquaresInCircles.safe_openRay_of_disjoint
#print axioms SquaresInCircles.open_arc_budget
#print axioms SquaresInCircles.ray_budget_impossible
#print axioms SquaresInCircles.OpenArc.third_distance_bounds
#print axioms SquaresInCircles.centers_distance_sq_ge_one
#print axioms SquaresInCircles.unit_contact

-- The two alternatives for three squares.
#print axioms SquaresInCircles.three_exterior_reduction
#print axioms SquaresInCircles.three_containing_impossible
#print axioms SquaresInCircles.three_compensation
#print axioms SquaresInCircles.near_axis_square_overlap

-- Seven squares: the marker arc, the gap of pi/3, the pair theorem for actual
-- squares, six markers, and the sliding packings.
#print axioms SquaresInCircles.Seven.marker_arc
#print axioms SquaresInCircles.Seven.fixed_gap_pos
#print axioms SquaresInCircles.Seven.SAT.separating_axes
#print axioms SquaresInCircles.Seven.marker_separation
#print axioms SquaresInCircles.Seven.six_markers_impossible
#print axioms SquaresInCircles.Seven.six_exterior_squared_lower
#print axioms SquaresInCircles.Seven.sliding_packing

-- Seven squares at the optimal radius: zeros at the gap of pi/3, closed
-- containment, the hexagon, the ring, the square in the middle, and the
-- classification.
#print axioms SquaresInCircles.Seven.Equality.fixed_gap_zero
#print axioms SquaresInCircles.Seven.fixed_gap_nonneg
#print axioms SquaresInCircles.Seven.Equality.all_gap_pos_below
#print axioms SquaresInCircles.Seven.Equality.marker_separation_closed
#print axioms SquaresInCircles.Seven.Equality.ordered_chart_contact
#print axioms SquaresInCircles.Seven.Equality.six_directions_hexagon
#print axioms SquaresInCircles.Seven.Equality.exists_containing
#print axioms SquaresInCircles.Seven.Equality.six_exterior_ring
#print axioms SquaresInCircles.Seven.Equality.central_square_represents
#print axioms SquaresInCircles.Seven.uniqueness
#print axioms SquaresInCircles.Seven.rigid_uniqueness
#print axioms SquaresInCircles.Seven.packing_iff_sliding
#print axioms SquaresInCircles.Seven.classification_by_slots

-- The statements being proved, for inspection.
#print SquaresInCircles.Packing
#print SquaresInCircles.HasNormalForm
#print SquaresInCircles.optimalRadius
#print SquaresInCircles.modelCenters
#check @SquaresInCircles.optimality
#check @SquaresInCircles.attainment
#check @SquaresInCircles.uniqueness
#check @SquaresInCircles.sliding_uniqueness
#check @SquaresInCircles.rigid_uniqueness
#check @SquaresInCircles.Five.polygon_uniqueness
#check @SquaresInCircles.Seven.marker_separation
#check @SquaresInCircles.Seven.sliding_packing
#print SquaresInCircles.Seven.Column
#print SquaresInCircles.Seven.slidingCenters
#check @SquaresInCircles.Seven.packing_iff_sliding
