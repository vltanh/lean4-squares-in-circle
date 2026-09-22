# Uniqueness of the optimal three-, four-, and five-square packings

## Status

This is an additive, **uncompiled Lean source development** based on the
compiled occupied-arc main commit:

`d7fa1f3c95e92ed6396d8c08d111ecf2427b66e3`.

The new theorem bodies have not been elaborated, compiled, or audited by Lean.
They may require library-interface or tactic corrections, and mathematical
mistakes are not ruled out by source inspection. No Lean, Lake, CI workflow,
external proof solver, or axiom audit was run while preparing this change.

Every new theorem has a proposed proof body. There are no admitted obligations,
custom axioms, or calls to `native_decide` in the extension. That is a property
of the written source, not evidence that Lean accepts the proof.

No existing repository file, packing definition, compiled proof, root import,
toolchain, or dependency manifest is changed. The legacy certificate machinery
is not restored or used. The entry points are separate for the three cases.

## Public entry points

```lean
import ThreeUnitSquaresInCircle.ThreeUniqueness
import ThreeUnitSquaresInCircle.FourUniqueness
import ThreeUnitSquaresInCircle.FiveUniqueness
```

Each namespace exposes `uniqueness` and `rigid_uniqueness`. The latter has an
explicit bijection of the plane preserving **Euclidean squared distance**, a
permutation of the squares, equality of closed square sets, and a condition
mapping the model's origin to the input disk center.

The three-square endpoint uses the original `Packing`. The n=4
and n=5 endpoints use the compiled `Unified.PackingN`. No new geometric,
contact, orientation, or certificate assumption is added to either predicate.

`FiveUniqueness.polygon_uniqueness` is stronger: it assumes only ordinary
interior-disjointness and the closed dodecagon constraints, not disk containment.

## Precise meaning of uniqueness

`Uniqueness.HasNormalForm S o centers` says that there are one angle `φ` and a
permutation `σ` such that, in the common rotated/translated coordinates
`pointInDirection o φ x y`, square `S (σ i)` is exactly the axis-parallel unit
square centered at `centers i`. Both its open and closed membership predicates
are specified. This deliberately does **not** equate `UnitSquare` records:
quarter-turn changes of a frame can represent the same geometric square.

The model centers, with the disk center at the origin, are:

* n=3: `(-1/2,-5/16)`, `(1/2,-5/16)`, `(0,11/16)`;
* n=4: `(1/2,1/2)`, `(-1/2,1/2)`, `(-1/2,-1/2)`, `(1/2,-1/2)`;
* n=5: `(0,0)`, `(1,0)`, `(0,1)`, `(-1,0)`, `(0,-1)`.

One rotation and translation suffice for these three models. Reflection is
not needed in the final witness: each model's reflected copies are rotationally
congruent after relabeling. Input charts still permit independent reversal.

`HasNormalForm.rigid_witness` constructs an actual `Point ≃ Point` and proves
its squared-distance identity. It never identifies the product-space norm on
`ℝ × ℝ` with the Euclidean norm.

## n=5: closed dodecagon rigidity

1. The compiled exterior-arc lemma is already strict under closed P5 inputs.
   The compiled safe-ray lemma also accepts closed octagon constraints.
2. If no square center equals o, the same five-arc budget contradicts the
   existence of the packing: exterior squares supply strictly more than 72
   degrees, and the possible containing square's ray supplies 72 degrees.
3. The dodecagon implies `a^2+b^2 ≤ 1`. For `s=a+b > 1`, use
   `|a-b| ≤ 3-2s` and
   `(s^2+(3-2s)^2)/2 = 1+(s-1)(5s-7)/2 < 1`.
4. Centers of disjoint unit squares have distance at least one. For equality,
   a supporting functional and Cauchy--Schwarz force both squares' axes to
   be parallel and the center displacement to be one common cardinal vector.
5. The centered square thus has precisely its four side-neighbors. Finite
   injectivity makes assignment to these five slots a permutation.

The center square's slack disk-containment constraint causes no degeneracy:
its position is forced by arcs and its orientation by the four contacts.

## n=4: actual containment eliminates the diamond's extra equality cases

The source does **not** claim uniqueness for the closed diamond alone.

1. The compiled strict Diamond Lemma guarantees at least one saturated tangent.
   The identity
   `phi a b - 2 = 2*(a+b-1)+(a-1/2)^2+(b-1/2)^2`
   then forces `a=b=1/2`: o is a vertex of that square.
2. Ordinary disjointness excludes o from the open interior of every square.
3. Use an auxiliary circle of radius **1/2** for equality analysis. For an
   exterior square set `u=2a-1`, `v=1-2b`. Actual containment gives
   `0 ≤ u < 2/3 < cos(pi/4)` and `u ≤ v ≤ 1`.
4. An occupied arc has length
   `min (2*arccos u) (arccos u + arcsin v)`. It is at least pi/2, and is
   strictly larger unless `a+b=1`.
5. The four-arc budget makes every tangent saturated, hence every square has
   o as a vertex. The four arc midpoints are quarter-turn spaced. Their
   local rectangles reconstruct exactly the four block slots.

The finite circular-order argument sorts the three nonzero principal angle
representatives. They are forced to `-pi/2`, `pi/2`, and `pi`.

## n=3: all boundary cases, without certificate tables

The strict optimality proof is not used as a uniqueness assertion. New closed
exterior lemmas explicitly retain their equality conditions.

1. At radius `5*sqrt(17)/16`, any square containing o in its open interior has
   **strict** contact tangents: equality in a tangent-plus-square-remainder
   identity would put it at a boundary contact type instead.
2. `three_containing_closed_impossible` allows closed exterior tangents and a
   deficit of zero. Strictness in the central tangent still makes clipped-cap
   compensation strict. If both exterior caps are full, the existing explicit
   near-axis overlap witness remains contradictory. Hence no square contains o.
3. The three exterior arc lengths are all at least 120 degrees; their budget
   forces equality. The two possible contacts are exactly:
   A = `(11/16,0)` and B = `(1/2,5/16)` in sorted absolute local coordinates.
4. Two A-contacts would overlap, using the compiled near-axis witness. Three
   B-contacts are impossible because, on a smaller auxiliary circle, each has
   an occupied semicircle. There is exactly one A and two B contacts.
5. The B semicircles force their radial phases to be antipodal. The three
   120-degree occupied arcs force the big-arc midpoints to be equilateral.
   Sine/cosine equations force the B chart reversals to be opposite and the
   A radial direction to be perpendicular to the B radial directions.
6. Both reversal alternatives are reconstructed into the same T slots, and
   all three possible labels of the A-square are handled explicitly.

No assumption about an occupied witness being the entire circle intersection
is inserted. Only containment of each witness and the shared angular budget
are used.

## Files and checking order

1. `Uniqueness/Basic.lean`: set-based normal forms, rigid equivalence,
   closed-set extension, finite slot reconstruction.
2. `Uniqueness/Angles.lean`: phase and interval helpers; quarter-grid rigidity.
3. `Uniqueness/Contacts.lean`: unit-distance contact rigidity.
4. `Uniqueness/Five.lean`: five-square polygon and disk uniqueness.
5. `Uniqueness/Four.lean`: four-square disk uniqueness.
6. `Uniqueness/ThreeClosed.lean`: closed caps and mixed containing-square case.
7. `Uniqueness/ThreeReconstruction.lean`: contact classification and T geometry.
8. `Uniqueness/Three.lean`: all-label assembly for n=3.
9. The three independent public entry points.

The optional `UniquenessAxiomAudit.lean` and `UniquenessSanityChecks.lean` are
provided for local iteration. Their existence is not a report of execution.
After the imports have been built, check the new endpoints and their axiom
lists. They should have only the standard dependencies, with no admission
axiom. This is an expected verification task, not a verified outcome.

The source-inspection JSON records only text-level checks. The compiled base
is not recompiled or modified by the source inspection.
