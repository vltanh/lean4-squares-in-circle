import SquaresInCircles.Seven.Uniqueness.Main

/-!
# Standalone entry point: n = 7, unique up to the sliding column

Public statements in `SquaresInCircles.Seven`:

* `uniqueness`: an optimal packing has a `SlidingNormalForm`.
* `uniqueness_column`: the explicit frame, permutation and `Column` witness.
* `rigid_uniqueness`: a Euclidean plane equivalence preserving both square sets.
* `packing_at_radius_iff`: exact classification of all attaining packings.
* `uniqueness_slots`: the nonnegative four-slot simplex parameterization.

All original n <= 5 entry points and the n = 7 optimality files are unchanged
by this extension. This entry point does not assert that the slot parameters
are unique modulo geometric symmetry.

The development is an uncompiled proof draft layered on the uncompiled
analytical optimality draft. No CI or workflow modification is included.
-/
