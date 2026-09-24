# Seven squares: uniqueness up to the sliding column

## Status and scope

This is a **complete proposed source-level proof chain, uncompiled**, stacked
on the analytical n=7 optimality draft in PR #4 at
`334e95324b54a836d72b356da9718c16c185f8ad`.

It is not a claim of Lean kernel acceptance. Neither this extension nor its
PR #4 dependencies have been compiled or axiom-audited as part of this work.
Elaboration, tactic, library-interface and possibly more substantial proof
repairs may be needed. The definitions, hypotheses and intermediate arguments
must be reviewed as well as the final theorem type.

The new PR's diff contains only equality/uniqueness source, optional unexecuted
audit/regression scripts, and this note. It makes no changes to CI workflows,
the toolchain, dependencies, existing n<=5 results, or PR #4's proof modules.
No CI result was inspected or used as a premise.

## Public entry point

```lean
import SquaresInCircles.Seven.Uniqueness
```

The principal declarations are in `SquaresInCircles.Seven`:

```lean
uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : SlidingNormalForm S o

rigid_uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : CongruentToSliding S o

packing_iff_sliding (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔ SlidingNormalForm S o
```

Here `radius = Real.sqrt (13/4)`. There is also
`uniqueness_sqrt_thirteen_half`, with the radius written `Real.sqrt 13/2`, and
`classification_by_slots`, using the exact simplex below.

There is no unproved marker, separator, contact, parallelism, equality-budget
or reconstruction hypothesis in these endpoint statements. Every intermediate
lemma has a proposed proof body; this does not establish that the bodies
elaborate.

## The classification is a family, not one packing

`SlidingNormalForm S o` means that there exists `c : Seven.Column` such that
`HasNormalForm S o (Seven.slidingCenters c)`.

The four side centers are

```
(1,-1/2), (1,1/2), (-1,-1/2), (-1,1/2).
```

The three middle centers are `(0,c.bottom)`, `(0,c.middle)`, `(0,c.top)` and obey

```
-sqrt(3)+1/2 <= bottom,
bottom + 1 <= middle,
middle + 1 <= top,
top <= sqrt(3)-1/2.
```

The normal form compares both open and closed square sets in a common frame.
It allows a global rotation/translation and a permutation. Individual
`UnitSquare` frame records are not equated: quarter-turning a square's frame
does not produce a new geometric packing. The explicit rigid witness carries
the normalized origin to the enclosing disk center.

`SlotSimplex` is the set of four nonnegative real numbers with sum
`2*sqrt(3)-3`. `columnSlotEquiv` is an explicit equivalence between `Column`
and that simplex, with both roundtrip identities proved in source.
The bottom, two internal, and top slots are independent subject to that single
sum constraint. No equal-spacing or circle-contact condition is added.

`SlidingNormalForm.packing` proves the converse using the preexisting
construction and the distance-preserving common frame. Hence the public
classification is an iff, not only a necessary condition.

## Equality proof architecture

### 1. Recover the scalar zero set

`ScalarEquality.lean` retains the positive remainders discarded in a lower-bound
proof. `FixedGapEquality.lean` follows every source axis, transverse sign and
active label through the fixed-gap partition.

The only directed contact types at marker gap pi/3 are:

1. lower side `(1,-1/2)` to upper side `(1,1/2)`;
2. upper side to an axial square;
3. axial square to lower side.

The axial square has zero transverse coordinate and arbitrary radial coordinate
in `[1/2,sqrt(3)-1/2]`. The proofs do not infer that coordinate from a strict
inequality.

For capped labels, all summands in the barycentric support formula are
nonnegative. A positive-weight summand must also be zero if the sum is zero.
Its active-label classification would require a side or axial marker, neither
of which is capped; this excludes the capped case without a strict-containment
assumption.

### 2. Extend angular separation to closed containment

The optimality proof was stated for strictly contained squares. Uniqueness
needs closed containment, so it cannot simply reuse that hypothesis.

`ClosedGaps.lean` first approximates a canonical state `(a,u)` by

```
((1-e)*a+e/2, (1-e)*u),    0 < e <= 1.
```

An exact quadratic identity gives strict admissibility. Continuity passes the
**scalar support inequalities** to the closed domain. This approximation is
not claimed to preserve square disjointness.

At gaps strictly less than pi/3, a leftmost zero would be an interior minimum.
Closed parallel-label inequalities exclude nonsmooth cardinal minima; the
existing nearest-corner argument excludes smooth minima. Thus all support
sums are still strictly positive at subcritical gaps.

`PairGeometry.lean` then uses the actual separating-axis theorem, in both
source frames, to prove closed marker separation for the original squares.
At an ordered gap exactly pi/3, a separator has zero support and therefore is
one of the three scalar equality contacts.

### 3. The angular budget produces a regular hexagon

`Hexagon.lean` sorts real lifts of six marker directions. The five successive
gaps and the wraparound gap are each at least pi/3 and sum to 2*pi. Their
nonnegative slacks therefore all vanish. The regular hexagon and every
successor identity, including the wraparound, are conclusions of the proof.

Seven exterior markers would already violate the angular measure budget.
Thus an optimal seven-square packing has exactly one origin-containing square.
Its center is not assumed to be the origin.

### 4. Reconstruct the six exterior squares

`ContactCycle.lean` encodes lower-side, upper-side and axial states by three
finite labels. Each zero contact advances to the next state. Up to cyclic
reindexing, the six labels must be

```
lower, upper, axial, lower, upper, axial.
```

The signed marker offsets determine the frame increments. After transporting
all frames by their quarter-turns, the exterior square centers are

```
(1,-1/2), (1,1/2), (0,h),
(-1,1/2), (-1,-1/2), (0,-k),
```

where both `h` and `k` are independently in `[1/2,sqrt(3)-1/2]`.
No parallel-frame premise is used; parallelism is an equality conclusion.

### 5. A short central-square rigidity argument

The central proof avoids the earlier tilted-tip/protrusion argument.

The four side squares are closed barriers in the band `|y|<=1`. A point of the
open central square with `|y|<1` cannot have `|x|>1/2`: its segment toward the
origin would cross one of those barriers. Closed-side/open-central separation
handles the barrier boundaries correctly.

Because the central square contains the origin, its center has squared norm
less than 1/2, so its center height is strictly inside the band. If both frame
coefficients are nonzero, their largest absolute value is less than one. The
horizontal section through the center then contains two interior points more
than one unit apart. That contradicts the width-one strip.

Thus its frame is parallel to the side columns. Applying the strip bound to
points approaching its horizontal side midpoints forces its horizontal center
to be zero. Its vertical center `z` remains free, with `|z|<1/2`.

`CenterSection.lean` proves the scalar section result;
`CentralSquare.lean` derives its hypotheses from the actual square geometry.

### 6. Recover precisely the sliding inequalities

The upper axial square, middle square and lower axial square are now aligned
in one column. Non-overlap gives

```
-k + 1 <= z,    z + 1 <= h.
```

Together with the two outer containment bounds these are exactly the fields of
`Column`. `Reconstruction.lean` uses an explicit omitted-label embedding and
finite injectivity to cover all seven squares, then invokes the existing
geometric normal-form construction. Every label is accounted for.

## Modules and review order

All new modules except the entry point are in `Seven/Uniqueness/`:

1. `NormalForm`, `Slots`.
2. `ScalarEquality`, `FixedGapEquality`.
3. `ClosedParallel`, `ClosedGaps`, `PairGeometry`.
4. `Hexagon`, `ContactCycle`.
5. `CenterSection`, `CentralSquare`.
6. `Reconstruction`.
7. `Seven/Uniqueness.lean`.

The separate `SevenUniquenessAxiomAudit.lean` and
`SevenUniquenessSanityChecks.lean` are supplied but were not run. An audit must
include both these modules and the dependencies from PR #4. No build or audit
success is reported by this PR.
