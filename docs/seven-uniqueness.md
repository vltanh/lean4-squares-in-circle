# Seven squares: uniqueness up to the sliding column

## Status and scope

This PR supplies an **end-to-end, uncompiled Lean source draft** for the
classification of every optimal seven-square packing. It is stacked on PR #4,
starting at commit `334e95324b54a836d72b356da9718c16c185f8ad` of
`vltanh/lean4-squares-in-circles`.

Neither this extension nor its analytical optimality dependency is claimed to
be kernel-verified. No Lean compilation, Lake build, axiom audit, or CI
inspection was performed. Elaboration, tactic, and potentially substantive
proof repairs may still be necessary. An unconditional theorem type and explicit
proof bodies are not evidence of kernel acceptance.

There are **no CI, workflow, toolchain, dependency, original root-import, or
original packing-definition changes** in the new PR. All commits are equality
proof work, interfaces, unexecuted checking scripts, or documentation.

## Entry points

```lean
import SquaresInCircles.Seven.Uniqueness
```

The convenience entry point adds explicit witnesses and aliases:

```lean
import SquaresInCircles.SevenUniqueness
```

The principal declarations, in `SquaresInCircles.Seven`, are:

```lean
uniqueness
  (S : Fin 7 -> UnitSquare) (o : Point)
  (hp : Packing S o radius) : SlidingNormalForm S o

rigid_uniqueness
  (S : Fin 7 -> UnitSquare) (o : Point)
  (hp : Packing S o radius) : CongruentToSliding S o

packing_iff_sliding (S : Fin 7 -> UnitSquare) (o : Point) :
  Packing S o radius <-> SlidingNormalForm S o
```

Here `radius = sqrt(13/4) = sqrt(13)/2`. There is no additional marker,
parallel-frame, contact-pattern, or classification hypothesis in these types.
`uniqueness_column` displays the column, common frame, permutation, and both
open and closed membership equivalences explicitly.

## The geometric conclusion

`SlidingNormalForm S o` means that there is a `Column c` and a single Euclidean
frame centered at `o` in which, after relabeling, the square sets have centers

```
( 1, -1/2), ( 1, 1/2), (-1, -1/2), (-1, 1/2),
( 0, c.bottom), (0, c.middle), (0, c.top).
```

All seven geometric frames are parallel in this representation. Individual
`UnitSquare` records are not equated; a quarter-turn of a square frame does not
produce a distinct square set.

The exact constraints on the middle column are

```
-sqrt(3)+1/2 <= c.bottom
c.bottom+1 <= c.middle
c.middle+1 <= c.top
c.top <= sqrt(3)-1/2.
```

Equivalently the four bottom/internal/top slots are nonnegative and sum to
`2*sqrt(3)-3`. `columnSlotEquiv` proves both directions of this parameterization.
`classification_by_slots` expresses the full packing classification in those
coordinates. Distinct slot vectors are NOT asserted to be inequivalent under
geometric symmetry.

The middle square need not be centered at the enclosing center. The convenience
entry point includes `off_center_sliding_attainment`, exhibiting a column with
strictly positive middle ordinate. The outer middle-column squares need not
touch the circle. No equal-spacing or equal-slot condition is imposed.

`CongruentToSliding` exposes a plane equivalence preserving `normSq` distances,
carrying `(0,0)` to `o`, and transporting both the open and the closed square
sets. Euclidean distance is not replaced by the product norm on `R x R`.

## Proof chain

1. **Closed parallel comparisons (`ClosedParallel`).** The contact-remainder
   inequalities are extended to non-strict containment. They stay strict when
   the marker gap is less than pi/3.
2. **Closed support gaps (`ClosedGaps`).** Convex interpolation of canonical
   coordinates extends the scalar support inequality to closed containment by
   continuity. This step does not assert that interpolation preserves packing
   non-overlap. A separate leftmost-zero argument supplies strict positivity
   at every subcritical gap; smooth and nonsmooth minima are both covered.
3. **Scalar zero sets (`ScalarEquality`, `FixedGapEquality`).** All positive
   sectors are excluded. The only directed zero contacts are lower-side to
   upper-side, upper-side to axial, and axial to lower-side. In each side--axial
   contact, the axial radial coordinate remains free on the entire admissible
   interval. Capped labels are handled by actual barycentric weights: a zero
   weighted sum must have a zero term with positive weight, which contradicts
   the uncapped contact classification.
4. **Original-square transport (`PairGeometry`).** Ordinary disjoint interiors
   give a separator in one of the two edge frames. The support inequality and
   its zero set are transported through the actual square charts, including
   reflected reverse order. No contact condition is added to `Packing`.
5. **Angular equality (`Hexagon`).** Six pairwise-separated directions are a
   regular hexagon. Sort real representatives and retain the six nonnegative
   gap slacks; their sum is zero, so each gap is pi/3. Seven separated directions
   are impossible. Hence an optimal seven-square packing has a unique square
   containing the enclosing center in its open interior.
6. **Exterior reconstruction (`ContactCycle`).** The three directed kinds force
   the six-cycle lower/upper/axial/lower/upper/axial. The frame increments recover
   four fixed side squares and the two sliding outer middle-column squares.
7. **Central rigidity (`CenterSection`, `CentralSquare`).** The four side squares
   form barriers throughout |y| <= 1, including their shared seam. Convexity
   confines the containing square to the width-one central strip in that band.
   Its center has |y| < 1. A tilted unit square has width greater than one in the
   horizontal section through its own center, so the square must be aligned.
   The strip then fixes its horizontal center coordinate to zero. This avoids
   the longer top-tip/circle-height estimate and leaves its vertical coordinate
   free.
8. **Whole packing (`Reconstruction`).** Non-overlap of the three aligned middle
   squares gives the two unit vertical gaps. Together with the ring's containment
   limits these are exactly the `Column` fields. Finite injectivity supplies the
   final relabeling and open/closed normal form.
9. **Converse and public interface (`NormalForm`, `Slots`, `Uniqueness`).** Every
   normal form is a genuine packing by the existing sliding construction and a
   Euclidean frame equivalence. The final theorem is therefore an equivalence,
   not only a necessary contact condition.

## Source organization

The primary dependency chain is the one listed above. Superseded alternative
proof files were removed from the branch tip to avoid duplicate declarations;
their text remains in the incremental Git history. The convenience `Main`
module imports the primary result and adds aliases, rather than declaring a
second `Seven.uniqueness`.

## Review scripts

`SevenUniquenessAudit.lean`, `SevenUniquenessAxiomAudit.lean` when present, and
`SevenUniquenessSanityChecks.lean` are supplied scripts, not executed reports.
They must only be described as audits after the imports have elaborated and
the audit commands have actually run. This PR does not modify any workflow to
run them.

The mathematical proof of classification is stronger than the previous
optimality claim. In particular, continuity alone does not classify equality,
and the old strict-containment pair theorem alone does not classify the closed
boundary case. Those are explicit additional lemma chains here, subject to
review and later Lean checking.
