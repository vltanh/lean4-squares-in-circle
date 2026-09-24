import SquaresInCircles.Seven.Uniqueness

/-!
Audit script only: this file has not been run. The proof depends on the
uncompiled PR #4 optimality/analysis development. An unconditional theorem
statement and absence of admission tokens do not establish kernel acceptance.
-/
#print axioms SquaresInCircles.Seven.Equality.fixed_gap_zero
#print axioms SquaresInCircles.Seven.Equality.all_gap_nonneg
#print axioms SquaresInCircles.Seven.Equality.all_gap_pos_below
#print axioms SquaresInCircles.Seven.Equality.marker_separation_closed
#print axioms SquaresInCircles.Seven.Equality.ordered_chart_contact
#print axioms SquaresInCircles.Seven.Equality.six_directions_hexagon
#print axioms SquaresInCircles.Seven.Equality.exists_containing
#print axioms SquaresInCircles.Seven.Equality.six_exterior_ring
#print axioms SquaresInCircles.Seven.Equality.central_square_represents
#print axioms SquaresInCircles.Seven.Equality.classify
#print axioms SquaresInCircles.Seven.uniqueness
#print axioms SquaresInCircles.Seven.rigid_uniqueness
#print axioms SquaresInCircles.Seven.packing_iff_sliding
#print axioms SquaresInCircles.Seven.classification_by_slots

#check SquaresInCircles.Seven.uniqueness
#check SquaresInCircles.Seven.CongruentToSliding
#check SquaresInCircles.Seven.columnSlotEquiv
#check SquaresInCircles.Seven.optimality_attainment_and_classification
