# A2 structural-first case tree

This file obeys the A2 hard gate: **no new stress lemma is introduced**.
Existing P9--P18 may be invoked only after separator logic / angle bounds
place a branch inside their stated hypotheses.

Work under a hypothetical counterexample with `R^2 < q_*`; hence all
`Q0`-level geometric bounds are available. The already-proved
local-rigidity neighborhood is terminal and is omitted below.

Write

    e=theta_E, n=theta_N, w=theta_W,
    d=theta_D, s=theta_S, eps=d-pi/4.

Bits are in the order `(E,N,W,D,S)`, with 1 = canonical own-primary and
0 = cardinal-preferred.

## 1. Common structural facts

The following are available before any A2 terminal stress family is invoked.

1. A1 and P7:

       D is own-primary,
       0 < d <= pi/4,
       -pi/4 < eps <= 0.

2. West-category cyclic order gives

       w <= d.

3. Any cardinal helper satisfies

       |theta| < 2/5.

4. If two opposite helpers are both cardinal, then

       E,W cardinal  => |e|+|w| < 4(rho0-1) < 23/50,
       N,S cardinal  => |n|+|s| < 4(rho0-1) < 23/50.

   Their two central-side depths add to one, while the cap-depth function
   obeys `B(t) <= B(0)-t/2` on `[0,2/5]`.

5. P6 gives

       E own => -5/12 < e < 3/10,
       N own => -3/10 < n < 5/12.

6. Separating-axis completeness: each outer pair separates on one of the four
   endpoint primary/secondary axes.

7. Existing P17--P18 may be invoked on

       0 <= w <= d <= pi/4,

   and then give

       d > pi/4-1/4,
       eps > -1/4,
       D--W = W-secondary.                         (DW+)

## 2. Disjoint forbidden-pattern partition

The nine forbidden canonical patterns are

    10,12,13,14,26,28,29,30,31.

Use the obstruction order **A2.3 -> A2.1 -> A2.2**.

### A2.3 first

`S_o and W_o` consists exactly of

    28,29,30,31.

### A2.1 second

After A2.3 is removed, `N_o and E_c` consists exactly of

    10,14,26.

Pattern 30 was the only overlap with A2.3.

### A2.2 last

After A2.3 and A2.1 are removed, `W_o and N_c` consists exactly of

    12,13.

Patterns 28,29 were the overlaps with A2.3.

Thus the structural classification splits disjointly as `4 + 3 + 2`.

## 3. A2.3 structural tree: patterns 28,29,30,31

Here

    W own, D own, S own.

The E/N bits are whatever the pattern specifies.

Split on the sign of `w`.

### A3+ : w >= 0

Because `w<=d`, (DW+) applies:

    eps > -1/4,
    D--W = W-secondary.

Separating-axis completeness leaves

    D--S in {D-primary,D-secondary,S-primary,S-secondary}.

No existing P9--P16 chain certificate applies because those relevant
certificates assume S cardinal. Thus A3+ is an explicit residual family.

### A3- : w < 0

P17--P18 do not apply. Separating-axis completeness leaves

    D--W in {W-primary,W-secondary,D-primary,D-secondary},
    D--S in {D-primary,D-secondary,S-primary,S-secondary}.

This is the second explicit A2.3 residual family.

**Current structural conclusion for A2.3:** no whole pattern is yet excluded
by separator/cap/marker geometry alone.

## 4. A2.1 structural tree: patterns 10,14,26

Common bits:

    E cardinal, N own, D own,
    -3/10 < n < 5/12,
    |e| < 2/5.

### Pattern 10 = (E_c,N_o,W_c,D_o,S_c)

E and W are opposite cardinal helpers, hence

    |e|+|w| < 23/50.

No existing P9--P18 family closes the whole branch because N is own.
This is an explicit A2.1 residual.

### Pattern 14 = (E_c,N_o,W_o,D_o,S_c)

Split on `w`.

- If `w>=0`, (DW+) gives `eps>-1/4` and `D--W=W-secondary`.
- If `w<0`, all four D--W source axes remain structurally possible.

One subfamily is already terminal by P9: if

    D--W=D-secondary,
    D--S in {D-secondary,S-secondary},
    |w|<=2/5,
    1/6<=s<=1/2,
    -1/3<=eps<=-1/6,

then P9 contradicts `R^2<=Q0`. The complement remains structural residual.

### Pattern 26 = (E_c,N_o,W_c,D_o,S_o)

Again E and W are opposite cardinal helpers:

    |e|+|w| < 23/50.

S is own, so the N/S-cardinal chain certificates do not apply. This is an
explicit A2.1 residual.

**Current structural conclusion for A2.1:** P9 removes one Pattern-14 tail,
but no whole one of 10,14,26 is yet excluded structurally.

## 5. A2.2 structural tree: patterns 12,13

The E bit is irrelevant to the N--W--D--S chain. Both patterns have

    N cardinal, W own, D own, S cardinal.

Therefore

    |n|,|s| < 2/5,
    |n|+|s| < 23/50.                               (NS-cap)

Split first on `w`.

### A22+ : w >= 0

By (DW+),

    eps > -1/4,
    D--W = W-secondary.                            (A22+)

Split on `s`.

#### A22+L : s >= 1/6

From (NS-cap),

    |n| < 23/50-1/6 = 22/75 < 3/10.               (A22-n)

Separate by the D--S source axis.

##### D--S = S-secondary

The whole n-range is already terminal:

    -3/10 < n <= -1/5   -> P16,
    -1/5 <= n <= 1/5    -> P15,
     1/5 <= n < 3/10    -> P11.

These lemmas allow the full `0<=w<=pi/4` range.

##### D--S = D-secondary and 0 <= w <= 1/5

Again the whole n-range is terminal:

    -3/10 < n <= -1/5   -> P16,
    -1/5 <= n <= 1/5    -> P14,
     1/5 <= n < 3/10    -> P12.

##### Remaining A22+L leaves

Only these remain open:

    R22-a: D--S is D-primary or S-primary;
    R22-b: D--S = D-secondary and w > 1/5.

These should be attacked first by source-axis geometry / pins / marker order,
not by a new stress.

#### A22+S : s < 1/6

None of P11--P16 has this lower-s domain as a stated hypothesis. Keep

    R22-c: w>=0, s<1/6, D--W=W-secondary,
           D--S any source axis.

Do **not** assume `s>=1/6`: diagnostic residual boxes reach below that
threshold, so it is not an established structural consequence.

### A22- : w < 0

P17--P18 do not apply. Keep

    D--W in {W-primary,W-secondary,D-primary,D-secondary}.

The old hand certificates cover several subrectangles, but they do not yet
form a complete structural cover. Record

    R22-d: w<0

as one explicit residual family.

Do **not** assume `w>=0`: a restricted diagnostic run of the current
non-stress contractions leaves many w<0 residual boxes.

## 6. Structural accounting

At whole-pattern level, **0 of the 9 forbidden patterns are currently
eliminated by pure separator/cap/marker geometry alone**.

What the structural-first pass has established is nevertheless useful:

- the nine patterns split disjointly as `4 + 3 + 2`;
- A2.2 on `w>=0, s>=1/6` is almost completely funneled into P11--P16;
- the only nonnegative-w / large-s A2.2 residuals are `R22-a` and `R22-b`;
- the additional A2.2 residuals are exactly `R22-c` (small s) and
  `R22-d` (negative w);
- A2.1 and A2.3 residuals are now explicit rather than hidden behind a guessed
  global stress family.

The next structural priority is `R22-a`: try to exclude the two D--S primary
source axes. Then attack `R22-b` by proving D-secondary forces
`w<=1/5` or by placing that leaf in an already-proved non-stress terminal
theorem. Only after those should `R22-c` and `R22-d` be revisited.
