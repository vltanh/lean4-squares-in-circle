# Incremental n=7 proof checkpoints

Work continues on PR #4, branch `draft/seven-analytic-lean`. Each lemma group is
committed before beginning the dependent group. The checkpoints below extend
`a0bdc7c9de193c6a93be1c8933e9f8576395eac9` without replacing prior work.

No compiler, Lake, CI-status inspection, or axiom audit was run for these
checkpoints. They are proposed proof bodies, not a report of Lean acceptance.
Commit messages use `[skip ci]`; this is not a claim about a workflow result.

## Saved groups

| Commit | File / result |
| --- | --- |
| `b952ef6f952d930247fa4ef31255455334103bcd` | `Seven/InwardTurnBounds.lean`: whole-interval positive- and negative-turn inequalities with rational margins. |
| `3662a71ba0df422562bfde24d18b21ec606a4c58` | `Seven/InwardSideAxial.lean`: derive the turn inequalities from the actual labels and support sum; obtain closed positivity, strict positivity, and equality conditions. |
| `0a37039c3213d6b0284b2aa06cd3aec183cf6df4` | `Seven/AxialProfile.lean`: connect the pre-existing polynomial certificates to the actual universal trigonometric profile, including zero and nonzero angles. |
| `309e6f80c0eb542e3d07f3d42d7acd52aef870b0` | `Seven/InwardAxialAxial.lean`: complete proposed source bodies for the inward-radial (+,+), axial/axial sector on its full admissible domain. |
| `2b198d85d652f83fa5c3e679ef39452abe532086` | `Seven.lean`: import these groups through the existing optional entry point. |

## Main new statements

With the existing `Admissible`, `StrictlyAdmissible`, `label`, `side`, `axial`,
`pairSupport`, and `remainder` definitions:

* `inward_side_axial_lower` retains the quantitative bound
  `2 * remainder a u / 15 + abs (label a u - label A v - pi/6) / 840`.
* `inward_side_axial_pos` needs strict containment only for the source side
  square. The axial target may already touch the candidate circle.
* `inward_side_axial_eq_zero` concludes `a = 1`, `u = 1/2`, `v = 0`.
  It does not constrain the target radial coordinate `A` to a single value.
* `axial_profile_pos` and `axial_profile_nonneg` prove the sign of
  `sin z - (4/5)*z*cos z - (7/8)*(1-cos z)` over `[0, pi/2]`.
* `inward_axial_axial_pos` is strictly positive under closed containment for
  both squares. Its zero-turn case is included, not discarded.

## What remains

These additions fill two axial-target cases of the inward-radial (+,+) sector.
They do not discharge the whole `FixedGapStatement`. The target-side case,
other mixed/sign sectors and their boundary-minimization arguments still need
assembly or further formalization. The intermediate-angle minimum argument
and the complete chart-to-geometric-pair transport also remain.

`Remaining.lean` already contains a proof body for `markerArc_proved`, from
work preceding these checkpoints. `MarkerSeparationStatement` is still not
proved, and `optimality_of_marker_separation` therefore remains conditional.
No unconditional `Seven.optimality` or verified n=7 axiom audit is claimed.

The new files contain no deliberate admission, custom axiom, native oracle,
or unchecked external success flag. This source property does not establish
that they elaborate or that all mathematical reductions are complete.
