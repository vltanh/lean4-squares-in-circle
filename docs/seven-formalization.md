# Seven squares: analytical Lean development

## Status

**Partial and uncompiled. This PR is not a completed Lean proof of the
seven-square optimum.** It supplies substantive proof scripts from the
analytical manuscript and the exact assembly that would finish the original
packing theorem once its remaining pair lemma is supplied.

Base: `1e873b0cc56853f4ec33f98db13340c77053806d` of
`vltanh/lean4-squares-in-circles`, using the existing Lean/mathlib v4.34.0 setup.
No original file, packing definition, proof, toolchain, root import or workflow
is changed. All new modules use the existing square and Euclidean-distance
model.

No Lean compiler, Lake build, or axiom audit was run while preparing the files.
The source can still contain elaboration, library-interface or tactic errors.
The absence of admission tokens is not a completion claim: the final lower
bound still requires the explicit, unproved `MarkerSeparationStatement`.

## Entry point

```lean
import SquaresInCircles.Seven
```

The old root entry point is unchanged and continues to state only its existing
results for n <= 5. There is intentionally no unconditional `Seven.optimality`.

## Supplied source bodies

| Module | Scope |
| --- | --- |
| `Seven/Construction.lean` | Candidate radius; the full sliding-column construction; its four nonnegative slots; packing and attainment; the side-corner lower bound for this fixed family. |
| `Seven/Labels.lean` | Canonical magnitude domain; affine labels; exact contact-remainder identities; strict and non-strict bounds; signed reflection; transfer to the repository's square charts. |
| `Seven/CircleBudget.lean` | Six directions cannot have every pairwise circular distance greater than pi/3, using the existing circle-measure theorem. No cyclic sorting needed. |
| `Seven/ExteriorSelection.lean` | Explicit embedding that discards at most one origin-containing square; preservation of packing. Boundary points remain exterior. |
| `Seven/ParallelLabels.lean` | Same-frame and quarter-turn label inequalities, including the min-label alternatives. These are the algebraic pair components, not a separate theorem about arbitrary rotations. |
| `Seven/TaylorBounds.lean` | Polynomial sine and cosine bounds from monotonicity of exact remainders. |
| `Seven/PolynomialCertificates.lean` | Whole-interval positivity via Bernstein identities, including the final degree-eleven discriminant and its quadratic consequence. |
| `Seven/Support.lean` | Marker-point membership, actual square-support domination, center bounds, outward radial support positivity, coordinate Cauchy--Schwarz. Marker-point membership is NOT the stronger marker-arc lemma. |
| `Seven/SideSide.lean` | Global opposite-sign side-selected/side-selected scalar support certificate, including strict containment. |
| `Seven/Reduction.lean` | Genuine original-packing lower-bound assembly, explicitly conditional on the missing concrete pair theorem. |
| `Seven/Remaining.lean` | Exact proposition definitions for the outstanding marker-arc, fixed-gap, and geometric reduction statements. These are not asserted as theorems. |

The polynomial coefficient data are finite rational identities checked by
`ring` and `norm_num` in the proposed Lean source. No Python/C++ verification
result, optimizer result, interval-search transcript, `native_decide`, or
custom axiom is imported as a proof premise.

## The remaining mathematical formalization

The analytical manuscript assigns

```
P(a,u) = min (5*u/4)
              (pi/6 + (u-1/2)/3 + 3*(1-a)/4)
              (pi/4)
```

and proves marker separation through an actual marker arc, an intermediate-angle
minimum argument, and an exhaustive fixed-gap support analysis. That chain is
not yet fully translated in this PR.

The three explicitly stated obligations are:

1. **MarkerArcStatement.** Prove closed-square membership throughout the
   half-width 801/1600 arc around the affine marker, not only at its midpoint.
   The subsequent proof must handle the finite square-boundary exceptions rather
   than assume the whole closed arc is interior.
2. **FixedGapStatement.** Finish all cardinal-axis, transverse-sign and active-label
   sectors at marker gap pi/3. This includes capped-label convex reduction,
   the remaining mixed axial/side cases, and the transition-state and
   monotonicity arguments. Positivity of a residual polynomial by itself does
   not prove the geometric reduction that produces that polynomial.
3. **GeometricReductionStatement.** Prove that the first two obligations imply
   the concrete pair-separation theorem for actual independently rotated squares.
   This requires the separating-axis reduction, intermediate-angle minima,
   chart/reflection transport, and strictness under strict containment.

`Remaining.lean` gives precise formulas, including all original square
hypotheses. None concludes `True`. None is an axiom or a theorem with an
unproved body. The definitions merely state the tasks.

The final conditional statement is:

```lean
Seven.optimality_of_marker_separation
    (hpair : Seven.MarkerSeparationStatement)
    (S : Fin 7 -> UnitSquare) (o : Point) (R : Real)
    (hp : Packing S o R) : Seven.radius <= R
```

An axiom audit of this conditional theorem does not discharge `hpair`.
The global lower bound is not formalized until that argument is actually
provided by a closed Lean proof.

## Sliding is represented, not excluded

`Seven.Column` has bottom, middle and top ordinates, with gaps at least one
and endpoints in `[-sqrt(3)+1/2, sqrt(3)-1/2]`. `Column.slots` maps it to four
nonnegative numbers summing to `2*sqrt(3)-3`. `columnOfSlots` builds the converse
construction. No uniqueness statement is asserted, and the middle square is
not assumed to be centered at the disk center.

The side squares use the box half-extents `(3/2,1)`. The middle-column squares
use `(1/2,sqrt(3))`; using `(3/2,1)` for all seven squares would be false.

## Checking order

These commands are supplied for checking, not reported as executed:

```sh
lake build SquaresInCircles.Seven
lake env lean SevenSanityChecks.lean
lake env lean SevenAxiomAudit.lean
```

The audit file includes the actual types of the outstanding propositions and
the conditional endpoint. It must not be summarized as an audit of an
unconditional optimality theorem. The optional source-inspection report records
only text/import properties and is not evidence of Lean acceptance.
