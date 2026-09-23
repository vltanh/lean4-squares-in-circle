import SquaresInCircles.Seven.Construction
import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Seven.ExteriorSelection
import SquaresInCircles.Seven.ParallelLabels
import SquaresInCircles.Seven.TaylorBounds
import SquaresInCircles.Seven.PolynomialCertificates
import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.MarkerArc
import SquaresInCircles.Seven.SideSide
import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Seven.Remaining

/-!
# Partial seven-square analytical formalization

The full canonical marker-arc proof has been added. The lower-bound endpoint
remains conditional on `Seven.MarkerSeparationStatement`: the fixed-gap sector
partition and geometric reduction are not yet completely formalized.

The optional entry point is built explicitly by CI. A green check for the old
root entry point alone does not verify this development. The sliding family
is retained; no uniqueness or isolated-optimum hypothesis is used.
-/
