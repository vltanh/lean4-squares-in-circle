# Standalone three-square occupied-arc proof

## Status

This change supplies explicit proof scripts for the formerly unwritten
origin-containing case and assembles the independent three-square arc proof.
There are no admitted declarations in the added source and no invocation of
`Cert.optimality` in the new proof or its adapter.

**The code is uncompiled.** No Lean compiler, Lake build, CI run, or axiom audit
was performed. Complete proposed proof bodies are not evidence of successful
elaboration or kernel acceptance. Library-interface, tactic, and mathematical
errors can still be discovered during review. The scripts target the existing
Lean 4.34.0 / mathlib v4.34.0 project configuration without changing it.

The exact claim formalized is the lower bound and attainment, not uniqueness.

## Separate entry point

```lean
import ThreeUnitSquaresInCircle.ThreeArc
```

This exposes:

```lean
ThreeUnitSquaresInCircle.ThreeArc.squared_lower
ThreeUnitSquaresInCircle.ThreeArc.optimality
ThreeUnitSquaresInCircle.ThreeArc.optimality_and_attainment
```

`optimality` takes the original `Packing S o R` hypothesis, with arbitrary
independent square rotations and an arbitrary disk center, and concludes
`optimalRadius ≤ R`. The entry point does not import the four-square or
five-square endpoints or the combined endpoint. The latter is retained as an
optional compatibility API, now using `ThreeArc.optimality` for its n=3 branch.
The original `ThreeUnitSquaresInCircle/Main.lean` is untouched.

A stronger intermediate statement is supplied:

```lean
Unified.three_polygon_strict_impossible
```

It rules out three disjoint squares all satisfying the strict contact 16-gon,
without assuming containment in a circle. This is not obtained from the old
certificate theorem, which concerns curved containment rather than the
stronger polygon relaxation.

## How all cases are covered

1. `ThreeExterior.lean`: If the tested point lies in none of the open square
   interiors, each square supplies an occupied open arc longer than 120 degrees.
   The shared angular budget yields a contradiction. Boundary points belong to
   this exterior alternative; no general-position assumption is made.
2. `ThreeContaining.lean`: If the tested point lies inside one square, ordinary
   disjointness excludes it from the other two. Every possible containing label
   is handled explicitly at the final assembly.
3. No exception assumes that the containing square's center is nonzero. A
   centered square already contradicts the first angular budget in this proof.
   The normalization inequalities used later follow from that budget.

## New modules and proof mechanism

### `Unified/ArcMetric.lean`

Proves that disjoint positive-width occupied arcs have midpoint distance at
least the sum of their half-widths, using an explicit point on a shortest
quotient-circle path. Also proves the elementary circle inequality

```
dist x y + dist y z + dist z x ≤ 2*pi.
```

Together these replace a separate circular-order or arc-tiling classification.
All arc witnesses concern actual membership in the planar regions. There is
no assertion about angular projections or an unproved null boundary.

### `Unified/ThreeCoordinates.lean`

Recovers arbitrary Cartesian membership from the existing square chart,
including reflected frames, by polar representation of a point. Supplies
coordinate change between two radial phases, the genuine inscribed-disk
inclusion, symmetric cap witnesses with their actual midpoint retained, and
an explicit intersection point for the final two squares.

In the first radial frame, the point is `(1/5, 2/5)` or `(1/5, -2/5)`, according
to the sign of the relative sine. This closes the overlap step by four strict
local-coordinate inequalities; no additional SAT or separator hypothesis is
inserted.

### `Unified/ThreeScalar.lean`

Proves monotonicity of

```
asin(1/2 + (16/13)*t) - asin(t)
```

on the required interval. The derivative proof explicitly establishes that
both square-root denominators are positive and ordered. This yields the
compensation inequality through the previously supplied sine-midpoint lemma.
The strict central tangent supplies the strict midpoint inequality, so no
strict-convexity equality classification is needed.

It also proves the deficit bound `delta < 1/12`, and a deliberately relaxed
radial estimate `u > 9/20`. The latter follows from the quadratic cosine bound,
avoiding a separate Lipschitz theorem. Both margins suffice for the overlap.

### `Unified/ThreeCaps.lean`

Constructs the containing witness of length

```
L = pi/2 + asin(P) + asin(Q),
P = (1/2-a)/(3/8), Q = (1/2-b)/(3/8), a >= b.
```

It is only a contained interval, not an assumed exact description of the
whole intersection. This distinction automatically handles configurations
where the actual circle intersection has additional components.

For an exterior square, it constructs the occupied clipped cap of length

```
min (2*A) (A+V),
A = acos((a-1/2)/(3/8)), V = asin((1/2-b)/(3/8)).
```

Disjointness from the central inscribed disk gives the radial-gap condition
needed in the compensation inequality. The three-arc budget excludes the
clipped alternative `V < A`. The surviving cap is symmetric around the
square's actual radial chart phase, with `b < 1/16` and `a <= 11/16`.

### `Unified/ThreeContaining.lean`

Combines the witnesses. Initially the two exterior arcs force `L < 2*pi/3`.
The containing deficit `delta = 2*pi/3-L` is less than `1/12`. Each clipped
neighbor would compensate for the entire deficit and violate the angular
budget. Both neighbors must therefore supply full caps.

Their midpoint separation lies between `2*pi/3` and `2*pi/3+1/12`. The circle
perimeter lemma supplies the upper bound; disjointness supplies the lower.
The corresponding relative cosine and sine satisfy

```
-3/5 < cos <= -1/2, 4/5 < |sin| < 7/8.
```

The explicit Cartesian witness then belongs to both exterior square interiors,
contradicting the input disjointness. This is the missing containing case.

## Checks supplied, not compiler results

`ThreeArcSanityChecks.lean` records exact rational margin tests and regression
statements. `ThreeArcAxiomAudit.lean` asks Lean to print the dependency axioms
of the critical lemmas and endpoint. Neither file was executed.

The accompanying JSON inspection report is textual only: file hashes,
admission-token scans, import checks, and the changed-path list. It does not
validate type checking, theorem statements, or kernel acceptance.

After local elaboration, the intended endpoint checks are:

```sh
lake build ThreeUnitSquaresInCircle.ThreeArc
lake env lean ThreeArcSanityChecks.lean
lake env lean ThreeArcAxiomAudit.lean
```

These commands are instructions for subsequent local iteration, not a record
of actions taken in preparing this change.
