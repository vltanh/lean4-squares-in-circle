import SquaresInCircles.Seven.Construction
import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Seven.ExteriorSelection
import SquaresInCircles.Seven.ParallelLabels
import SquaresInCircles.Seven.TaylorBounds
import SquaresInCircles.Seven.PolynomialCertificates
import SquaresInCircles.Seven.Support
import SquaresInCircles.Seven.MarkerArc
import SquaresInCircles.Seven.EasySectors
import SquaresInCircles.Seven.SideSide
import SquaresInCircles.Seven.InwardAxialAxial
import SquaresInCircles.Seven.SeparatingAxes
import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Seven.Remaining

/-!
# Partial seven-square analytical formalization

The full canonical marker-arc proof and several whole-domain support sectors
have proposed proof bodies. The new inward-radial positive-sign sector includes
side-selected/axial-selected and axial-selected/axial-selected states, with the
zero-turn case and the axial sliding equality included explicitly.

The lower-bound endpoint remains conditional on `Seven.MarkerSeparationStatement`:
the complete fixed-gap partition and geometric reduction are still being
formalized. These additional source bodies have not been compiled.

The sliding family is retained; no uniqueness or isolated-optimum hypothesis
is used. See `docs/seven-checkpoints.md` for incremental saved work.
-/
