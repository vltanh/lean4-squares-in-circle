# Verification

[Back to the README](../README.md)

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SanityChecks.lean
```

Requires Elan/Lake and network access for mathlib. The build uses Lean `4.34.0`
and mathlib `v4.34.0`. The source contains no `sorry`, no `axiom` declarations
and no `native_decide`.

- `lake build` must report zero `declaration uses 'sorry'` warnings.
- Every `#print axioms` line in the audit must read exactly
  `[propext, Classical.choice, Quot.sound]`.
- `sorryAx` in that output would indicate an unproved lemma;
  `Lean.ofReduceBool` would indicate `native_decide` and compiler trust.
- The audit also prints `Packing`, `optimalRadius`, `HasNormalForm`,
  `modelCenters` and the theorem signatures for inspection.
- `SanityChecks.lean` checks the radius and centre tables, re-proves the exact
  rational margins the proofs rely on, restates the public theorems, and checks
  all five optimal packings against their normal forms; it must elaborate
  without errors.

[`.github/workflows/lean.yml`](../.github/workflows/lean.yml) runs these steps
on every push to `main` and on pull requests, using `leanprover/lean-action`.
Its axiom audit covers every declaration under `SquaresInCircles`, not only the
ones printed by `AxiomAudit.lean`.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved.

**Trusted base:** Lean, Lake, mathlib. Every numeric margin is an exact rational
inequality closed by `norm_num`, `linarith` or `nlinarith`; `π` enters only
through mathlib's rational bounds `3.14 < π < 3.1416`. There are no
machine-generated certificates.
