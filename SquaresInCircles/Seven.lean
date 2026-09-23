import SquaresInCircles.Seven.Construction
import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Seven.ExteriorSelection
import SquaresInCircles.Seven.ParallelLabels
import SquaresInCircles.Seven.TaylorBounds
import SquaresInCircles.Seven.PolynomialCertificates
import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.SideSide
import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Seven.Remaining

/-!
# Partial seven-square analytical formalization

The unconditional results include attainment (with the sliding family), affine
label algebra, polynomial certificates, the side--side support sector, and the
six-marker counting theorem. The lower-bound endpoint is explicitly named
`Seven.optimality_of_marker_separation` and still has an unproved pair-theorem
hypothesis. There is no unconditional `Seven.optimality` in this module.

See `docs/seven-formalization.md` for the exact outstanding obligations and
validation status. Importing this file does not extend the existing n <= 5
optimality or uniqueness definitions.
-/
