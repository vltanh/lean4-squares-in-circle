# Roadmap: close unrestricted n=6

This is the fixed proof plan. Do not switch proof frameworks unless one of the numbered lemmas below is actually false.

## Phase A — Finish global structural reduction

### A1. Force D to use its own-primary separator from C — CLOSED

Proved in `research/six/A1.md` under the original `c_x,c_y >= 0` normalization.

If D were west-cardinal, W must be own-primary because at most one square may use a central side. The problem reduces to the two angles `(theta_W,theta_D)`.

The former two-angle interval replay has been replaced by a hand concavity argument. Axis-specific rational three-separator stresses reduce every one of the eight directed W--D SAT axes to a gap
`C+F(theta_W)+G(theta_D)+H(theta_D-theta_W)`. On each of the three sign chambers the pieces are concave, so the minimum is attained at one of seven fixed chamber vertices.

`research/six/check_A1_hand.py` checks only the scalar curvature inequalities and the 56 fixed endpoint evaluations with exact rational/Taylor arithmetic. There is no interval subdivision; the smallest certified endpoint gap is (>1/500).

No center-coordinate search is used. The original sector/pin normalization is preserved for A2.

### A2. Collapse the remaining central-separator patterns modulo local rigidity

The raw bit implications are not treated as standalone geometric statements: own-primary and cardinal separation meet on the candidate boundary. The correct classification is radius-sensitive.

Starting from D own-primary, prove:

**Outside the already-proved 1/100 full-dimensional local-rigidity neighborhood, every candidate-sized packing has central pattern**

    8, 9, 11, 15, 24, 25, or 27.

Equivalently, outside the local neighborhood establish the three implications

- N own implies E own;
- W own implies N own;
- S own implies W cardinal.

Near the candidate no bit-classification lemma is needed: local rigidity already proves R^2 >= q_* regardless of which endpoint supplies a tied separator.

Target: reduce the nonlocal central-pattern analysis to the seven observed patterns without a 17-variable search.

Deliverable: a short radius-sensitive classification theorem, with only low-dimensional scalar/stress checks if needed.

## Phase B — Classify outer separating axes

For each remaining central pattern, use separating-axis completeness and the existing angle/cap bounds.

### B1. D-W classification

Show every possible D-W separator lands in one of:
- candidate graph;
- alternate D-W hand lemma;
- both-D-secondary hand lemma.

### B2. D-S classification

Do the symmetric classification.

### B3. W-N and S-E classification

Show their possible source axes are exactly those already allowed by the hand certificates.

Deliverable: every normalized packing receives one of a small finite set of contact-graph labels.

No interval search.

## Phase C — Close every labeled graph analytically

Current status:

| Family | Status |
|---|---|
| Local candidate neighborhood | proved |
| Five-parallel/full-angle | proved |
| One-oblique-pair | proved |
| Four-side small-angle | proved |
| Opposed T-junction | proved |
| Alternate D-W | hand reduction essentially done |
| D-W,D-S both D-secondary | hand reduction essentially done |
| Large-angle candidate graph | hand reduction essentially done |

### C1

Finish polishing the alternate D-W scalar inequalities.

### C2

Finish the second alternate-D scalar inequalities.

### C3

Finish the large-angle endpoint proof.

Computer assistance in Phase C is restricted to checking explicit rational/Taylor arithmetic. No recursive multidimensional subdivision.

## Phase D — Coverage theorem and unrestricted optimality

Prove explicitly:

**If R^2 < q_*, the configuration belongs to one of the families in Phase C.**

Invoke the corresponding lower bound in every case to obtain a contradiction. This establishes R_6^2 >= q_*.

Combine it with the explicit candidate packing to obtain **R_6 = sqrt(q_*)**.

Phase D is the point at which unrestricted n=6 optimality is actually closed.

## Phase E — Equality and uniqueness

Only after Phase D.

Trace equality through the branch theorem and determine whether the known five-aligned-plus-45-degree packing is unique up to Euclidean, labeling, and quarter-turn symmetries.

Uniqueness must not delay the optimality theorem.

## Phase F — Lean

Only after the paper proof is complete.

Reuse the existing repository machinery for:
- separating axes;
- charts and markers;
- containment;
- elementary trigonometry;
- rational/Taylor inequalities;
- the verified n=7 exterior theorem.

Formalization order: **A -> B -> C -> D -> E**.

Do not compile continuously while developing the mathematics.

## Working rules

1. No new proof framework unless a roadmap lemma is demonstrated false.
2. Do not return to the 17-variable branch-and-bound search.
3. Do not use a large five-dimensional interval search.
4. Numerical optimization may locate a certificate but is never a proof premise.
5. Prefer hand monotonicity/concavity. Otherwise use a tiny exact rational scalar certificate.
6. Commit after each completed lemma.
7. Report progress by roadmap label: A1, A2, B1, B2, B3, C1, C2, C3, D, E.
8. Do not work on uniqueness or Lean until D is closed.

## Immediate task

**A2 only: collapse the remaining central-separator patterns.**

Do not move to Phase B until A2 is proved or one of its proposed implications is replaced by the precise correct statement.
