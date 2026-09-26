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

##### Structural lemma S1: D--S primary axes are impossible

On A22+L, neither D-primary nor S-primary can separate D from S.  This is a
direct projection argument; no new stress is used.

Put

    t=d-s,     delta=d-w,
    H(q)=(1+cos q+sin q)/2,
    B=117/250,     a0=177/200.

From (A22+) and `1/6<=s<2/5`,

    27/200 < t < 5/8,      0<=delta<=pi/4.         (S1-range)

The first inequality uses `pi>157/50`; the second uses `pi<19/6`.
Also `rho0<28/25`.

For the forced W-secondary D--W separator, let

    z(q)=a_D sin q+b_D cos q.

The fixed W/D pins determine the orientation of this separator: the D pin has
larger W-secondary projection because the W-to-D pin chord points at 285
degrees, while W-secondary has angle `270 degrees+w`.  Therefore

    z(delta)-b_W > H(delta).

Since `b_W>-B`,

    z(delta)>H(delta)-B.                           (S1-DW)

**S-primary.**  The signed D--S center difference on S-primary is

    U=a_S-z(t).

Its negative side is harmless:

    z(t)<rho0 sin t+B cos t<57/50,

so `U>-51/200>-H(t)`.

For the positive side put `u=s-w`, so `delta=t+u`.

- If `u<=0`, then `t>=delta`.  The function z is increasing on
  `[0,pi/4]`, since
  `z'(q)>=a0 cos q-B sin q>(a0-B)/sqrt(2)>0`.
  Hence `z(t)>1-B=133/250`, and
  `U<28/25-133/250<1<H(t)`.

- If `u>0`, solve (S1-DW) for `b_D` and substitute at t:

      z(t)
        > [cos t (H(delta)-B)-rho0 sin u]/cos delta.

  On `[0,pi/4]`, `H(q)>=1+q/4`.  Using
  `cos t>81/100`, `t>27/200`, `u<2/5`, and
  `rho0<28/25` gives

      z(t) > 36503/400000.

  But

      rho0-H(t)
        < 28/25-(1+27/800)
        = 69/800
        = 34500/400000.

  Thus again `U<H(t)`.

So S-primary cannot separate.

**D-primary.**  The relevant signed difference is

    V=a_D-a_S sin t+b_S cos t.

Again `V>-51/200>-H(t)`.  If `b_S<0`, the upper bound is already
`V<H(t)` from `t>27/200`.

Assume `b_S>=0` and put

    c=cos s, q=sin s,
    C=1/2+c-(rho0-1),
    R_s=sqrt(Q0-C^2),
    U0=a_S+1/2, V0=b_S+1/2.

S-cardinality and containment imply

    U0 c-V0 q >= C,
    U0^2+V0^2 <= Q0.

Consequently

    V0 <= c sqrt(Q0-C^2)-Cq,

and direct substitution yields

    V-H(t) <= G(d,s),

where

    G(d,s)
      = rho0-1/2 + R_s cos d-C sin d-cos(d-s).     (S1-G)

For fixed s,

    partial_d G
      = -R_s sin d-C cos d+sin(d-s)
      < -627/2000 < 0,

using `C>261/200`, `cos d>7/10`, and `sin(d-s)<3/5`.
Hence the maximum is at `d0=pi/4-1/4`.

At d0, direct differentiation gives

    G_ss
      = cos s sin d0 + cos(d0-s)
        + cos d0 [C cos s/R_s-Q0 sin^2 s/R_s^3].

Here `rho0-1>1/10` gives `R_s>9/10`; therefore

    G_ss
      > (23/25)(47/100)+23/25-480/729
      > 0.

So `G(d0,s)` is convex and its maximum is at `s=1/6` or `s=2/5`.
Elementary rational Taylor bounds give

    G(d0,1/6) < -1531/20000,
    G(d0,2/5) <  -837/20000.

Thus D-primary cannot separate either.

Therefore on A22+L,

    D--S in {D-secondary,S-secondary}.             (S1-axis)

##### Structural lemma S2: D-secondary forces w <= 1/5

Assume instead that D--S uses D-secondary.  If `w>1/5`, put again

    delta=d-w,     t=d-s.

Since `w>1/5` and `d<=pi/4`,

    0<=delta<pi/4-1/5<59/100.                      (S2-range)

From the W-secondary D--W separation (S1-DW),

    b_D
      > [H(delta)-B-a_D sin delta]/cos delta
      >= [H(delta)-B-rho0 sin delta]/cos delta.    (S2-bD)

The signed D--S difference on D-secondary is

    Y=a_S cos t+b_S sin t-b_D.

Its negative side is harmless because `Y>-2B>-1>-H(t)`.

For the upper side, using `a_S<=rho0`, `b_S<B`, and (S2-bD),

    Y-H(t)
      < A(t)-N(delta)/cos delta,

where

    A(t)
      =(rho0-1/2)cos t+(B-1/2)sin t-1/2,

    N(delta)
      =H(delta)-B-rho0 sin delta.

Since `B<1/2`, `cos t<=1`, and `rho0<28/25`,

    A(t) < 3/25.                                   (S2-A)

On `0<=delta<59/100`, elementary Taylor bounds give

    cos delta > 83/100,
    sin delta < 14/25.

Therefore

    N(delta)-(3/25)cos delta
      = 4/125 +(19/50)cos delta
        -(rho0-1/2)sin delta

      > 4/125 +(19/50)(83/100)
        -(31/50)(14/25)

      = 1/5000 > 0.                                (S2-N)

Thus `N(delta)/cos delta>3/25`, contradicting (S2-A).
So D-secondary separation is impossible whenever `w>1/5`.

Hence on A22+L the D-secondary branch automatically has

    0 <= w <= 1/5,

and is terminal by P16/P14/P12.

##### Consequence for A22+L

Combining S1 and S2, **every** branch with

    w>=0,    s>=1/6

is now closed:

- S-primary and D-primary are structurally impossible (S1);
- D-secondary forces `w<=1/5` (S2), then P16/P14/P12 apply;
- S-secondary is terminal by P16/P15/P11.

No A22+L residual remains.

#### A22+S : s < 1/6

Here S-cardinality gives `-2/5<s<1/6`.  Keep

    delta=d-w,    t=d-s,    H(q)=(1+cos q+sin q)/2.

By (DW+),

    0<=delta<=pi/4,
    d>pi/4-1/4.

Hence

    11/30 < t < 6/5 < pi/2.                        (S3-range)

The first two rational bounds follow from `157/50<pi<19/6`.

##### Structural lemma S3: S-primary is impossible throughout A22+S

As in S1, put

    z(q)=a_D sin q+b_D cos q.

The forced W-secondary D--W separation gives

    z(delta)>H(delta)-B >= 1-B = 133/250.          (S3-DW)

Let

    U=a_S-z(t)

be the signed D--S difference on S-primary.

Its negative side is harmless. Since `0<t<pi/2`,

    z(t)<rho0+B<397/250,

so

    U>a0-(rho0+B)>-703/1000>-1>=-H(t).

For the positive side it is enough to prove

    z(t)>rho0-H(t).

Because `H(t)>=1` and `rho0-1<3/25`, it suffices to show
`z(t)>3/25`.

Put `r=w-s=t-delta`.

- If `r>=0`, then

      z(t)=z(delta) cos r+z'(delta) sin r.

  On `0<=delta<=pi/4`,

      z'(delta)
        =a_D cos delta-b_D sin delta
        >=a0 cos delta-B sin delta
        >(a0-B)/sqrt(2)>0.

  Also `0<=r<pi/4+2/5<6/5`.  The fixed scalar bound
  `cos(6/5)>7/20` therefore gives

      z(t)>(133/250)(7/20)=931/5000>3/25.

- If `r<0`, put `u=s-w=-r`. Then `0<u<1/6` and
  `t=delta-u<pi/4`. Solving (S3-DW) for `b_D` and substituting at t gives

      z(t)
        > [cos t (H(delta)-B)-rho0 sin u]/cos delta.

  Since `cos t>1/sqrt(2)>7/10`, `H(delta)>=1`,
  `rho0<28/25`, and `sin u<u<1/6`,

      z(t)
        > (7/10)(133/250)-(28/25)(1/6)
        = 1393/7500
        > 3/25.

Thus `|U|<H(t)`, so S-primary cannot separate D from S anywhere in A22+S.

##### S2 also extends to A22+S

The proof of S2 used the lower bound `s>=1/6` only to keep
`t=d-s` in a range where `sin t>=0`.  By (S3-range) we still have

    0<t<pi/2.

Therefore the same argument applies verbatim: if D--S uses D-secondary and
`w>1/5`, then

    Y-H(t)
      < A(t)-N(delta)/cos delta,

with `A(t)<3/25` and `N(delta)/cos delta>3/25`, a contradiction.
Hence

    D--S=D-secondary  =>  0<=w<=1/5.               (S3-Ds)

##### Residual after S3

The small-s residual is first reduced structurally to

    w>=0, -2/5<s<1/6, D--W=W-secondary,
    D--S in {D-primary,S-secondary},
    or D--S=D-secondary with 0<=w<=1/5.

The D-primary branch is then excluded by the two-edge hand stress
`A2.2 hand lemma — the small-s D-primary branch` in `A2.md`.

The D-secondary branch is also closed without a new stress: the existing
P12/P14/P16 D-secondary chain stresses remain separately concave after
enlarging their S-angle interval to [-2/5,1/6].  The exact extension checker
has worst endpoint margin greater than 0.0074216.

Therefore the only remaining small-s branch is

    R22-c:
      D--S=S-secondary, 0<=w<=d.

The exact adjacent-pair source checker then removes every alternate W--N and
S--E source.  It is enough to keep only

    W--N in {W-primary,N-secondary},
    S--E in {S-primary,E-secondary}.

Thus R22-c now consists of four equality-source graphs per central pattern,
all sharing the same committed tangent-coercivity estimate.

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
- A2.2 on `w>=0, s>=1/6` is completely closed by S1--S2 plus P11--P16;
- the only A2.2 residuals are now `R22-c` (nonnegative w but small s) and
  `R22-d` (negative w);
- A2.1 and A2.3 residuals are now explicit rather than hidden behind a guessed
  global stress family.

The next structural priority is `R22-c`: understand the small-s branch
without assuming a false lower bound.  After that, refine the negative-w
family `R22-d`.
