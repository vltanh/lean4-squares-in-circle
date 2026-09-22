# Unified arc formalization: extension draft

**Status: uncompiled and incomplete. There are six explicit `sorry` proofs, all in
`ThreeUnitSquaresInCircle/Unified/ArcGeometry.lean`.** The new optimality statements
are draft endpoints, not newly kernel-verified theorems. The other new proof
scripts have not been elaborated and may require additional repairs.

Base repository: `vltanh/three-unit-squares-in-circle`.
Base commit: `4f73fefceb73e8e707c837f55549bf864f0dfd8a`.
Target: the repository's existing Lean/mathlib **v4.34.0**.

No existing file is changed. In particular, the original `Packing` definition,
`Cert.optimality`, library entry point, toolchain, lockfile, and axiom audit are
untouched. The extension is opt-in:

```lean
import ThreeUnitSquaresInCircle.Unified
```

## Scope implemented in source

* `Basic.lean`: `PackingN` for an arbitrary index type, definitionally equivalent
  to the existing `Packing` when the index type is `Fin 3`; exact farthest-vertex
  containment; local absolute center coordinates. Euclidean lengths use the
  repository's `normSq`, not the product type's supremum norm.
* `Tangents.lean`: one exact tangent identity; strict and nonstrict reductions for
  the three-square 16-gon, four-square diamond, and five-square dodecagon.
* `Support.lean`: octagon support bounds for **arbitrary normals**, using only the
  repository's general support separator, followed by safe radial extension.
  The target square's octagon constraint alone suffices for the extension lemma.
* `AngularMeasure.lean`: actual occupied-angle sets on a half-open period, their
  Lebesgue measures, and the finite disjoint-family angular budget. Open-square
  intersections are used so that the budget needs no boundary-nullness theorem.
* `ScalarArcs.lean`: inverse-trigonometric midpoint inequalities, a strict
  three-square scalar arc bound, the deficit estimate, rational near-cap overlap
  witness, and selected five-square radical margins.
* `SafePieces.lean`: replace the unique origin-containing square by the interior
  of its safe extension; keep the other open squares. The resulting measurable
  pieces remain disjoint.
* `Cases.lean`: complete *assemblies* conditional through the six admissions,
  with explicit `_draft` names.
* `Constructions.lean`: block and plus constructions, and reuse of the existing
  T construction, independent of the admitted arc lemmas.
* `Main.lean`: compatibility with the established three-square theorem, plus the
  new, still admitted unified endpoint.

These descriptions refer to written proof bodies, not successful Lean checking.

## Exact remaining obligations

| ID | Declaration in `ArcGeometry.lean` | Remaining mathematics to formalize |
|---|---|---|
| G3-E | `exterior_three_mass` | Normalize the frame and prove the actual occupied-angle measure equals the clipped-cap formula; apply the already scripted scalar bound. |
| G3-I | `containing_three_caps` | The containing-square deficit/compensation argument, circular ordering of the other arcs, reframing, and construction of a `NearCaps` witness. |
| G4-E | `exterior_four_eventually` | Exterior arc formula, its equality case, and a left-neighborhood radius perturbation. |
| G4-I | `extension_four_eventually` | A quarter-arc in the radial extension, strict interior after contracting the radius, and its measure consequence. |
| G5-E | `exterior_five_mass` | The exterior arc formula and maximization of the two-arcsine sum on the dodecagon's three boundary segments. |
| G5-I | `extension_five_mass` | Inclusion of the radius-1/2 disk in the extension and conversion of its strict 72-degree cap inclusion into a measure lower bound. |

G3-I is the largest gap. The six statements are substantive proof obligations;
they are not merely library-name or compiler-version issues. Every new arc lower
bound depends on two of them; `unified_optimality_draft` depends on all six.

No uniqueness classification for the attaining configurations is formalized in
this extension. The endpoint asserts lower bounds plus existence of attaining
packings, not uniqueness.

## Two changes from the informal proof

**Four squares.** Work at radii just below `sqrt 2 / 2`. The equality quarter-arcs
become strictly longer; a finite intersection of left neighborhoods provides one
common radius. This avoids classifying the many diamond-tight configurations.

**Three squares.** The final two near-radial caps overlap at an explicit point:
`(1/5, 2/5)` in the first radial frame. `near_caps_point` proves the four strict
local-coordinate inequalities from the cap bounds. The remaining geometry must
still construct and transport that frame and point; the `NearCaps` record does
not assume point membership.

## Dependency separation

```
Geometry -----------------> Basic -> Tangents -> Support
SeparatingAxes ------------------------------------^
Basic -> AngularMeasure -----------+---------------+
                                  |               |
                                  v               v
                            SafePieces       ScalarArcs
                                  \               /
                                   ArcGeometry  [six admissions]
                                        |
                                      Cases
                                        |
Construction -> Constructions ------> Main <--- existing Main
```

The old `Cert.optimality` is used only in `three_radius_lower_existing`, a clearly
labeled compatibility theorem. It is NOT used to claim that the new three-square
arc argument has been completed.

## Validation status

No Lean compiler, `lake build`, axiom audit, interval optimizer, or Python
mathematical verifier was run for this extension. Source-only inspection checks
file inventory, import paths, comment-stripped admission counts, and dependency
reachability. It is not proof validation.

For the next local iteration, these are the intended commands (not executed by
the author of this draft):

```bash
lake build ThreeUnitSquaresInCircle.Unified
lake env lean UnifiedAxiomAudit.lean
```

Successful compilation with the six admissions still present would not establish
the new optimality results. Their axiom lists would include `sorryAx`. The new
`UnifiedAxiomAudit.lean` deliberately includes both independent core results and
all six admitted declarations, so that this distinction is visible.

The immediate implementation target is a reusable rectangle/circle intersection
measure lemma, including rotation/reflection invariance. It feeds G3-E, G4-E and
G5-E; extension cap-measure lemmas then feed G4-I and G5-I. The compensation and
arc-order argument G3-I remains separate.
