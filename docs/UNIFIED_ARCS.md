# Unified arc development for three, four, and five unit squares

## Status and scope

This is an **uncompiled source extension** of commit
`4f73fefceb73e8e707c837f55549bf864f0dfd8a`, targeting the repository's
Lean 4.34.0 / mathlib v4.34.0 configuration. No Lean compiler, Lake build,
axiom audit, or CI workflow was run while preparing it. It is a draft for
elaboration and review, not a claim of kernel acceptance.

The original geometry, certificate tables, final three-square theorem,
construction, root import, toolchain, and dependency manifest are unchanged.
New declarations live in `ThreeUnitSquaresInCircle.Unified`.

| Result | What this extension supplies |
| --- | --- |
| Three-square exact lower bound | An adapter to the existing compiled `Cert.optimality` theorem. |
| Independent three-square arc proof | Exterior occupied-arc theorem and exterior-only contradiction; the containing-square compensation step is **not formalized here**. |
| Four-square lower bound | Proposed end-to-end arc proof body, with strict diamond inequalities and a slightly shrunken auxiliary circle. |
| Five-square lower bound | Proposed end-to-end arc proof body, with dodecagon inequalities and auxiliary radius `5/6`. |
| Four- and five-square attainment | Explicit block and plus constructions in the original square model. |
| Unified endpoint | `optimality_and_attainment_345`; its n=3 branch still uses the original certificate proof. |

Every supplied theorem has an explicit proof body; no `sorry`, `admit`, custom
`axiom`, or `native_decide` is used. **This does not establish that the source
elaborates.** Tactic failures, library-interface corrections, or mathematical
errors may still be found. In particular, do not describe this as a completed
independent arc formalization of all three cases.

## Public statements

`PackingN S o R` has precisely the original geometric conditions, generalized
from `Fin 3` to `Fin n`: a nonnegative radius, containment of every closed unit
square, and disjoint open interiors. There is no separator, tangent, arc,
certificate, or lower-bound assumption in the packing predicate.

```lean
three_optimality : PackingN S o R -> optimalRadius <= R
four_optimality  : PackingN S o R -> Real.sqrt 2 <= R
five_optimality  : PackingN S o R -> Real.sqrt (5 / 2 : Real) <= R
```

The exact declarations use `ℝ` and Unicode inequalities. The combined API is:

```lean
optimality_and_attainment_345 (n : Nat) (hn : n = 3 ∨ n = 4 ∨ n = 5)
```

It gives the universal lower bound and an attaining packing for that n.
No equality classification or uniqueness theorem is claimed.

## Shared geometric development

`Basic.lean` keeps Euclidean squared lengths explicit as `normSq`. The norm on
`ℝ × ℝ` is NOT used as Euclidean length. It proves the farthest-vertex formula
`phi (alpha S o) (beta S o) <= R^2` from actual square containment.

`Tangents.lean` supplies the exact tangent-plus-square-remainder identity and
both strict and non-strict polygons: the three-square contact 16-gon, the
four-square diamond, and the five-square dodecagon.

`Support.lean` strengthens the previous exposition. For **any** nonzero
normal n, not only an edge normal, the support of the local center octagon
of S is at most `width S n + width T n`. The proof uses invariance of squared
length under the two frames. Thus the repository's existing general
`Cert.support_separator` theorem is sufficient. There is no new separating-axis
enumeration to formalize. `safe_openRay_of_disjoint` is derived from ordinary
interior-disjointness, not from a new assumption inside `PackingN`.

`AngularBudget.lean` works on `Real.Angle = AddCircle (2*pi)`. An `OpenArc` is
an actual angular metric ball whose circle points belong to a specified planar
region. Closed balls have Haar measure twice their half-width. Shrinking open
arcs by a common factor and taking an elementary supremum gives the budget
`sum halfWidth <= pi`. Counting angular shadows or assuming non-occlusion is
avoided, as are unproved boundary-null-set assertions.

`Charts.lean` transports the actual membership predicate into a square's local
frame, including independent rotations, reflections, coordinate swaps, and
translation back along its center ray. `Regions.lean` chooses the actual open
square except at the unique origin-containing square, where it chooses its
safe radial sweep.

## Four squares: remove equality bookkeeping by shrinking the radius

The fixed-radius diamond proof has several equality families, so it is not
correct to assume that only the block is tight for the relaxation. This draft
avoids that equality classification entirely.

For a hypothetical strict diamond packing, choose a common auxiliary radius
r slightly below `1/sqrt(2)`, above `1/2`, and outside every canonical near
corner. Such an r exists because the family is finite and all relevant
inequalities are strict. Every exterior square then has an occupied arc
strictly longer than 90 degrees, including squares with an axial center.
An origin-containing square has a safely swept quarter-circle at this r.
The four regions violate the shared angular budget.

The proof of the ray claim constructs the nonnegative translation parameter
from three strict half-plane inequalities; it does not assume a winding-count
or hidden combinatorial lemma.

## Five squares: use a rational auxiliary radius

The earlier mathematical note used `sqrt(7/10)`. Here the auxiliary radius is
`5/6`. The same geometric mechanism works with sufficient strict margin, and
the analytic bookkeeping is simpler:

* `arcsin x <= x + x^3/4` on `[0,3/5]`, proved using mathlib's cubic sine bound;
* a rational bound `sqrt 5 < 2237/1000`;
* `cos t > 401/500` for `|t| <= pi/5`, proved from the quadratic cosine bound;
* `sin (pi/5) < 3/5`, deduced from the same cosine bound and the unit identity.

These prove an exterior arc longer than 72 degrees. The radial sweep of an
origin-containing square contains a disk of radius 1/2 whose center is at
distance `1/sqrt(2)` from the tested point. That disk contains a 72-degree arc
on the auxiliary circle. The centered-square exception is excluded under
strict octagon inequalities using the general separating functional.

## Exact remaining n=3 obligation

`ThreeExterior.lean` proves an occupied arc longer than 120 degrees for every
exterior square under the strict contact polygon. It also proves that a
hypothetical strict polygon packing must contain the tested point inside one
square. Its truncated-arc bound uses a sine-addition inequality; no derivative
maximization is needed.

The following independent geometric step remains to be formalized:

> If three disjoint unit squares all satisfy the strict contact 16-gon and
> the tested point lies inside one square, the arc deficit of that square
> either forces an excess arc from a neighbor, or forces the two exterior
> squares into the near-axial configuration in which all four separating axes
> overlap.

The scalar final projection margins are already in `three_projection_margins`.
Still needed are the containing-square arc representation, its deficit bound,
the compensation dichotomy, transport of the resulting center/angle bounds,
and the geometric overlap conclusion. The existing n=3 certificate theorem
is a backstop for the public optimum endpoint, **not a proof of this stronger
polygon statement**.

## Suggested checking order

No commands below were executed during preparation.

Use the repository's existing dependency setup, then elaborate modules in this
order: Basic, Tangents, Support, AngularBudget, Charts, ElementaryTrig,
RectangleArcs, FiveScalar, RadialDisk, Regions, Five, FourScalar, FourRay, Four,
Constructions, ThreeExterior, Main.

The optional entry point is `ThreeUnitSquaresInCircle/Unified.lean`. Once its
imports elaborate, check `UnifiedSanityChecks.lean` and `UnifiedAxiomAudit.lean`.
For example:

```sh
lake env lean ThreeUnitSquaresInCircle/Unified.lean
lake env lean UnifiedSanityChecks.lean
lake env lean UnifiedAxiomAudit.lean
```

Dependent `.olean` files need to have been built first with the normal Lake
module targets. Keep the existing `AxiomAudit.lean` as a regression check.
The original three-square result should continue to report only the same
standard axioms; that is an expected check, not an audit result reported here.
