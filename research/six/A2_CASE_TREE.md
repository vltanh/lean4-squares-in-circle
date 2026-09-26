# A2 structural-first case tree

No new stress lemma is permitted in this file. Existing P9--P18 may only be invoked after a branch is placed in their hypotheses by structural geometry.

## 1. Disjoint pattern partition

With D own-primary fixed, the nine forbidden canonical patterns are

    10,12,13,14,26,28,29,30,31.

Use the obstruction order A2.3 -> A2.1 -> A2.2, not numeric order.

1. A2.3 (`S_o and W_o`) consists exactly of

       28,29,30,31.

2. After those are removed, A2.1 (`N_o and E_c`) consists exactly of

       10,14,26.

   Pattern 30 was the only overlap with A2.3.

3. After A2.3 and A2.1 are removed, A2.2 (`W_o and N_c`) consists exactly of

       12,13.

   Patterns 28,29 were the overlaps with A2.3.

Thus the structural classification can be proved by three disjoint branches of sizes 4,3,2.

## 2. A2.2 branch after the disjoint partition

Patterns 12/13 have, independently of E,

    N cardinal, W own, D own, S cardinal.

Write

    n=theta_N, w=theta_W, d=theta_D, s=theta_S,
    eps=d-pi/4.

Pure structural inputs already proved:

- `0 < d <= pi/4` (P7);
- west-category cyclic order gives `w <= d`;
- N,S cardinal cap bounds give `|n|,|s|<2/5`;
- the opposed-cardinal cap estimate gives `|n|+|s|<23/50`.

On the structural subbranch `w>=0`, the already-existing P17--P18 axis lemmas may then be invoked:

    eps > -1/4,
    D--W = W-secondary.

To place this branch into the already-proved P11/P12 hand certificates it remains to prove, without a new stress:

    G1. w cannot be negative;
    G2. w <= 1/5;
    G3. n >= 1/5;
    G4. s >= 1/6;
    G5. D--S has only the two secondary source axes {D-secondary,S-secondary}.

Then the cap bounds give automatically

    1/5 <= n < 2/5,
    0 <= w <= 1/5,
    1/6 <= s < 2/5,
    -1/4 < eps <= 0,

and P11/P12 exclude the two D--S choices for every W--N source axis.

The old diagnostic survivor strip suggests G1--G5, but it is not a proof and is not to be cited as one.

## 3. Remaining branches

A2.3 must be handled structurally first for patterns 28,29,30,31. After it is closed, A2.1 only has patterns 10,14,26. No A2.2 proof should spend effort on patterns 28/29.
