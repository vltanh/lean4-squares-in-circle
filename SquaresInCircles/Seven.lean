import SquaresInCircles.Seven.Optimality
import SquaresInCircles.Seven.Remaining

/-!
# Seven independently rotated unit squares

Standalone analytical proof entry point. The public statements are:

* `Seven.squared_lower`
* `Seven.optimality`
* `Seven.optimality_sqrt_thirteen_half`
* `Seven.six_exterior_squared_lower`
* `Seven.six_exterior_lower`
* `Seven.attainment`
* `Seven.optimality_and_attainment`
* `Seven.sliding_packing` and `Seven.sliding_is_optimal`

The lower-bound endpoints no longer take a marker-separation or support
hypothesis. Every link is represented by a draft proof body in the imported
modules: canonical marker arcs, the full fixed-gap partition, intermediate-
angle minima, finite-axis separation, chart transport, and the angular budget.

The original root entry point for n <= 5 is unchanged. No n=7 uniqueness
statement is asserted; the entire three-parameter sliding construction remains
available.

This is an uncompiled source draft. No Lean build, CI check, or axiom audit was
run while writing the completion. Elaboration, tactic, or proof repairs may
still be necessary; source completeness is not kernel verification.
-/
