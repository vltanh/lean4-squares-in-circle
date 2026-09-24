# Seven squares: end-to-end analytical Lean source draft

## Status

The three previously external proof obligations now have draft proof bodies.
The standalone entry point exports **unconditional** `Seven.optimality` and
`Seven.optimality_and_attainment` for the repository's original `Packing`
predicate. Neither theorem takes a marker, support, normal-selection, interval
certificate, or other geometric hypothesis beyond packing.

**This is a completed source-level draft, not a kernel-verified theorem.** No
Lean compiler, Lake build, CI inspection, or axiom audit was run while writing
this completion. Elaboration, library-interface, tactic, and potentially more
substantial proof repairs may still be needed. The existence of an explicit
proof body does not establish Lean acceptance.

Work was saved incrementally to the existing `draft/seven-analytic-lean` branch.
The completion starts from `0d99802b3a55f424cbed09b7ae61c12060c0c23e`; the original
project base was `1e873b0cc56853f4ec33f98db13340c77053806d`. No new toolchain or
external interval checker is introduced. The original n <= 5 root entry point
is not changed by this completion.

## Standalone API

```lean
import SquaresInCircles.Seven
```

The public namespace is `SquaresInCircles.Seven`:

```lean
squared_lower (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
  (hp : Packing S o R) : (13 : ℝ) / 4 ≤ R^2

optimality (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
  (hp : Packing S o R) : radius ≤ R

optimality_sqrt_thirteen_half ... : Real.sqrt 13 / 2 ≤ R

optimality_and_attainment :
  (∀ S o R, Packing S o R → radius ≤ R) ∧
  ∃ (S : Fin 7 → UnitSquare) o, Packing S o radius
```

Here `radius = Real.sqrt (13/4)`. The stronger `six_exterior_squared_lower` and
`six_exterior_lower` assume six original unit squares, their actual packing,
and that the specified disk center belongs to none of their open interiors.

`Remaining.lean` retains its old proposition names for compatibility, but now
supplies `markerArc_proved`, `fixedGap_proved`, `geometricReduction_proved`,
and `analytic_obligations_proved`. They are no longer inputs to the public
lower-bound theorem.

## Complete proof chain

### 1. Containment and angular labels

`Labels`, `ArcAnalysis`, and `MarkerArc` contain the canonical state bounds,
exact tangent-plus-square-remainder identities, and actual closed-square arc
of half-width 801/1600 around the piecewise-affine label. The definition uses
the square's own frame; independent rotations are not discarded.

### 2. Every fixed-gap support sector

`FixedGap.lean` is the exhaustive four-axis/four-sign assembly. It calls:

- `EasySectors`: outward, backward, and negative-source inward axes;
- `ForwardPositive`: positive/positive transverse source;
- `OppositeForward`: negative/positive transverse source, all A/T pairs;
- `ForwardNegativeTarget`: positive/negative, and axial-source negative/negative;
- `ForwardBothNegative`: side-source negative/negative, including the small-margin
  transition-state minimization;
- `InwardSideTarget`: positive/positive inward source with a side target;
- `InwardSideAxial` and `InwardAxialAxial`: its remaining axial-target cases;
- `InwardOpposite`: all positive/negative inward cases.

`CapReduction` handles the third, capped label by an exact barycentric triangle
argument. Strictness is propagated from the original states, not incorrectly
assumed for an endpoint chosen during minimization.

### 3. Exact boundary minimization and scalar signs

`LabelBoundary` defines the transition constants as radicals in pi and gives
explicit circular label-level parametrizations. `BoundarySegments` proves the
actual axial/side feasible segments and their support endpoints.

`TargetBoundaryMonotonicity`, `BoundaryProfiles`, and `ForwardBothNegative`
prove whole-interval monotonicity/concavity and the negative/negative support
minimum. `AnalyticOrder` supplies the real-analysis order lemmas.

`BoundaryPointChecks` proves the two fixed radical/trigonometric comparisons
using rational bounds for pi and proved finite Taylor polynomials. These are
fixed-point algebraic estimates, not configuration-space sampling.

`InwardOppositeGeometry`, `InwardBoundaryMinima`, and `InwardCircularCertificate`
handle the final mixed sector. The radical bound is proved by squaring an
explicit quadratic envelope. Its final polynomial is connected to
`PolynomialCertificates.radialE_pos`, rather than left as an unrelated
positive polynomial.

### 4. Intermediate marker gaps

`SmallAndParallelGaps` proves positivity for gaps at most one using **three
common closed-circle points**. If a support sum were nonpositive, the normal
would have the same projection at all three points. Trigonometric identities
would force both its sine and cosine to vanish. This avoids an additional
finite-boundary-null-set lemma.

At nonsmooth minima, the target normal is cardinal. The relative frame is zero
or pi/2 in the relevant interval, so the complete parallel-label inequalities
apply.

`AngularMinima` selects a **leftmost global minimizer**. This explicitly handles
constant sign pieces: a flat interval cannot create an unclassified interior
case. Fermat's theorem plus a left-neighbor comparison forces the target
sinusoid's smooth minimum to be negative.

`NearestCornerMinimum` then identifies its direction as opposite the target's
nearest corner. The sole potentially small source support is shown, using the
affine label and elementary sine/cosine inequalities, to exceed that corner's
distance. Thus the total support is positive even there.

`AllGaps.all_gap_support_pos` assembles endpoints, cardinal minima, and smooth
minima. No `GeometricReductionStatement` is assumed in this argument.

### 5. From scalar supports to the actual squares

`CanonicalPair` derives strict overlap on the first square's axes. Reversing
and reflecting the pair derives the second square's axes. The existing proved
`Seven.SAT.separating_axes` then produces a point in both open canonical squares.

`MarkerSeparation` transfers that point through `SquareChart.cartesian` and
`pointInDirection_transition`. A chart reversal becomes a signed transverse
coordinate. The `Real.Angle.toReal` difference chooses the positive marker
order; the negative case swaps the two charts. This proves the actual
`MarkerSeparationStatement`, not just a scalar surrogate.

### 6. The angular budget and original packing endpoint

The already written `CircleBudget` shows that six markers cannot all have
pairwise circular distance greater than pi/3. `ExteriorSelection` discards at
most one origin-containing square from a seven-square packing, preserving the
original containment and disjointness predicates.

`Optimality` supplies the now-proved marker theorem to that assembly. The
unconditional endpoint has no additional geometric assumptions.

## Sliding and equality scope

`Column` contains the three middle ordinates, with the two unit-spacing
inequalities and endpoint bounds `[-sqrt(3)+1/2, sqrt(3)-1/2]`.
`Column.slots` gives four nonnegative gaps summing to `2*sqrt(3)-3`;
`columnOfSlots` gives the converse construction. `sliding_packing` and
`sliding_is_optimal` cover every such column.

The boundary side–axial estimates leave the axial radial coordinate free over
its full admissible interval. The lower-bound proof needs strictness only in a
strictly smaller enclosing disk. It does not force an isolated optimum.

No classification of all equality packings or n=7 uniqueness theorem is
asserted by this extension.

## Validation boundary

No compilation or CI work was performed in this completion. The audit and
sanity scripts were updated to reference the unconditional endpoints but were
not run. The old `docs/seven-source-inspection.json` records an earlier partial
snapshot and must not be treated as a report for the completed branch.

The intended future checks, not executed here, are:

```sh
lake build SquaresInCircles.Seven
lake env lean SevenSanityChecks.lean
lake env lean SevenAxiomAudit.lean
```

The new proof bodies do not import Python/C++ success flags, interval-search
transcripts, native evaluation or custom axioms. The whole-interval polynomial
certificates are exact identities and coefficient signs expressed as ordinary
Lean proofs. Until elaboration and kernel checking succeed, none of these
source properties establishes the optimality theorem as machine-verified.
