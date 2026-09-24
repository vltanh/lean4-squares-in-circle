# Six unit squares: current global reduction and verification plan

## Status

This is research/proof progress toward the unrestricted \(n=6\) optimum. It is
**not** a proof of six-square optimality and is not imported by the Lean
library.

The verified \(n=7\) theorem on \`main\` is now used as a rigorous starting
point: six squares exterior to a specified disk center require squared radius
at least \(13/4\). Since the known six-square candidate has squared radius
below \(13/4\), every hypothetical improvement has a unique square containing
the disk center.

No CI/workflow/toolchain change is part of this branch.

## Candidate

Put

\[
 h=1/\sqrt2,\qquad
 A=(1466+1940h)/267,\qquad B=(327+432h)/712,
\]

\[
 s={2B\over A+\sqrt{A^2-4B}},\qquad
 t=(-20+30h)s+{7\over2}-{9h\over2},
\]

\[
 d={1\over2}+h-t,\qquad
 q_*=2s^2+4s+{5\over2}.
\]

The intended root is isolated by

\[
 .084<s<.085,\quad .420<t<.421,\quad .786<d<.787.
\]

The candidate centers, in the normalized frame, are

\[
 C=(s,s),\ N=(s,s+1),\ E=(s+1,s),\
 W=(s-1,t),\ S=(t,s-1),\ D=(-d,-d).
\]

The first five square frames are parallel; \(D\) is at angle \(\pi/4\).
The exact active containment identities are

\[
 q_*=(s+1/2)^2+(s+3/2)^2
     =(3/2-s)^2+(t+1/2)^2
     =2d^2+2hd+1/2.
\]

Numerically, only for orientation,

\[
 \sqrt{q_*}=1.688542968202\ldots .
\]

## Global facts already established analytically

The following are the strongest reductions currently available. The proof
manuscripts from which they were derived should be reviewed independently
before they are promoted to a formal theorem.

### 1. Unique containing square

For a packing below the candidate, exactly one square \(C\) contains the disk
center \(O\) in its open interior. Existence follows immediately from the
verified \(n=7\) six-exterior theorem; uniqueness follows from pairwise
interior-disjointness.

Normalize \(O=0\) and use \(C\)'s frame as the coordinate axes.

### 2. Central square is tightly centered

For \(R\le169/100\), put

\[
 \rho=\sqrt{R^2-1/4}-1/2.
\]

A support-core/forbidden-arc argument proves

\[
 |C_x|,\ |C_y|\le \rho-1,
\]

and, in a convenient rational form over the global working range,

\[
 |C_x|,\ |C_y|<23/200.
\]

This is a global statement: no contact graph, small-angle assumption, or
candidate neighborhood is assumed.

### 3. Every exterior square is side-nearest

For each exterior square choose an oriented edge frame \(e,f=Je\) and write
its center

\[
 p=a e+b f,\qquad a\ge |b|.
\]

Then

\[
 2-\rho\le a\le\rho,\qquad
 |b|<117/250<1/2,\qquad a+|b|<34/25.
\]

Hence the nearest point to \(O\) lies in the relative interior of the near
edge, never at a corner.

The affine marker from the verified \(n=7\) proof therefore simplifies
throughout this state domain to

\[
 \widehat\phi=\phi+{5b\over4}.
\]

The side and capped pieces of the seven-square marker are strictly inactive.

### 4. At most one outer square per central side

The cap-piercing lemma proves that two outer squares cannot both lie beyond
the same side of \(C\). This is valid for arbitrary square orientations and
does not require outer bounding boxes to be disjoint.

### 5. Only two possible central separator types per exterior square

Assign an exterior square to the nearest cardinal direction \(v\) of \(C\)'s
frame. Separating-axis completeness plus the preceding coordinate bounds
eliminate the opposite primary axis, the secondary square axis, and the two
wrong cardinal axes.

The separator between \(C\) and that outer square is therefore either

1. the corresponding cardinal normal \(v\), or
2. the square's own primary edge normal \(e\).

This is the discrete \(2^5\) branch structure used by the verifier.

### 6. Forced cyclic order and five interior pins

After reflections/interchange of axes, the five outer squares have a fixed
cyclic labeling \(E,N,W,D,S\).

On the auxiliary circle \(r=9/10\), the five squares contain these points in
their **open** interiors:

\[
\begin{array}{c|c|c}
E&(r,0)&0^\circ\\
N&(0,r)&90^\circ\\
W&r(-\cos15^\circ,\sin15^\circ)&165^\circ\\
D&r(-1/\sqrt2,-1/\sqrt2)&225^\circ\\
S&r(\sin15^\circ,-\cos15^\circ)&285^\circ .
\end{array}
\]

This is stronger than merely knowing sector membership. It is used as an
interval contraction in the current verifier.

### 7. Consecutive verified-marker gaps

The cyclic order of the five occupied arcs agrees with the order of the
simplified affine markers

\[
 \phi_i+5b_i/4.
\]

Every consecutive gap is strictly between

\[
 \pi/3\quad\hbox{and}\quad 2\pi/3.
\]

The lower bound is inherited from the verified seven-square pair theorem; the
upper bound follows because five positive gaps sum to \(2\pi\).

## Sharp branch results already proved on paper

These do not cover the whole global state space, but they are used as
terminal analytic certificates by the planned verifier.

### A. Full-dimensional local rigidity

In a \(1/100\) neighborhood of the candidate, with all five relative
orientations and all twelve center coordinates free,

\[
 R^2\ge q_*+
 {1\over40}\sum_{i=N,E,W,S,D}|\theta_i|
 +{1\over10}\sum_{i=N,E,W,S,D}|\xi_i|^2.
\]

Thus a verifier does not need to subdivide indefinitely near the exact
candidate.

### B. Full-angle five-parallel branch

If \(C,N,E,W,S\) are parallel and the eight candidate branch separators hold,
then the sixth square may have **arbitrary** orientation and arbitrary center
position. One obtains

\[
 R^2\ge q_*,
\]

with equality only at the candidate.

### C. One-oblique-pair branch

If, in the common frame of \(C\), at most one pair of square bounding boxes
overlaps in both coordinate projections, then compression to an aligned
packing preserves a genuine packing and the full-angle branch applies.
Therefore this entire class satisfies \(R^2\ge q_*\).

### D. Four-side small-angle branch

If four distinct neighbors are centrally side-separated and all four helper
angles and the diagonal deviation are at most \(1/24\), a translation-free
stress identity gives

\[
 R^2\ge q_*+
 {1\over32}\sum |\theta_i|.
\]

This branch allows multiple oblique outer pairs.

### E. Opposed T-junction branch

If a minimizer has the two opposed T-junctions present in the candidate, the
five corresponding frames are forced parallel. A barrier lemma then forces the
sixth square into the remaining southwest branch, and the full-angle theorem
proves \(R^2\ge q_*\).

The missing fact is **not** the algebra once that contact structure is known;
it is global coverage.

## Current computational target

The raw packing has 17 continuous variables after removing global rotation.
The analytical reduction above is intended to avoid certifying that space
directly.

The current verifier works with the normalized family

\[
 C_x,C_y,\qquad
 (\phi_i,a_i,b_i)_{i=E,N,W,D,S},
\]

but contracts \(a_i,b_i\) aggressively using:

* candidate-radius containment;
* the five open pin constraints;
* side-nearest bounds;
* the fixed cyclic marker order;
* marker gaps in \([\pi/3,2\pi/3]\);
* the \(2^5\) discrete central-separator alternatives;
* separating-axis rejection for all ten outer pairs.

Terminal boxes are intended to be discharged by one of:

1. a direct containment contradiction;
2. an unavoidable square overlap;
3. an impossible pin/marker ordering;
4. one of the already-proved branch theorems A--E;
5. a branch-specific convex-dual lower bound \(R^2\ge q_*\).

The current code is diagnostic, not yet a proof certificate. It records boxes
using rational decimal endpoints and supports checkpoint/resume so a complete
cover can later be independently checked or translated to Lean.

## What remains

A complete proof still requires one of the following:

* exhaust every normalized box and preserve a replayable certificate; or
* discover a global branch-independent inequality while inspecting the small
  set of surviving boxes.

The current branch should therefore be cited as **proof progress and verifier
infrastructure**, not as a proof of unrestricted \(n=6\) optimality.


## Verifier strengthening after the initial draft

The following consequences of the analytical reduction are now being used to
shrink the computer cover. They are mathematical constraints, not numerical
heuristics.

### Moving cap-piercing points

After the normalization C_x,C_y >= 0, the distinguished east and north
squares contain P_E=(C_x+1,0) and P_N=(0,C_y+1) in their open interiors,
whether their separator from C is cardinal or their own primary normal.

If an outer square actually uses a cardinal side of C, the cap-piercing lemma
supplies the corresponding moving interior point as well: P_W=(C_x-1,0) and
P_S=(0,C_y-1). These point constraints directly contract the local coordinates
a,b against C_x,C_y,phi.

In particular W and D, the two west-primary-category squares, cannot both use
the west cardinal side: the global cap theorem already proves at most one
square per side of C.

### Sharp cap-depth angle constraint

For a cardinally separated helper with acute deviation theta in [0,pi/4] from
that cardinal axis, its possible cap depth is at most

    B_R(theta) = (rho-1/2) cos(theta) - (1/2) sin(theta)
                 when R sin(theta) <= 1/2,
               = R - cos(theta) - sin(theta)
                 when R sin(theta) >= 1/2.

This function is decreasing. The verifier can reject a whole angle box as soon
as the minimum required central-side depth exceeds B_R(theta_min).

For four cardinal helpers this immediately reproduces theta_i < 2/5 and the
opposite-side sums

    theta_E + theta_W <= 4(rho-1),
    theta_N + theta_S <= 4(rho-1).

On a 50,000-box diagnostic run of the candidate separator pattern, adding
these already-proved constraints reduced the depth-48 unresolved boxes from
1,693 to 79 before further search-order changes. This count is diagnostic
only; it is not a proof statistic.

### Canonical separator patterns

The original 32-pattern search allowed overlapping descriptions: a square
could be placed in an own-primary branch even when its cardinal separator was
also available. The cover can instead be made canonical: choose the cardinal
separator whenever it is available, and use the own-primary branch only where
the cardinal margin is strictly negative. A cardinal boundary tie belongs to
the cardinal branch. This preserves full coverage while reducing duplicated
continuous regions.

### Exact arithmetic core

research/six/n6_exact_intervals.py is the first replay-oriented component. It uses
only Python integer/rational arithmetic for its proof-relevant calculations:

* pi is enclosed from Machin's identity pi = 16 atan(1/5) - 4 atan(1/239),
  using alternating rational series;
* sine and cosine are enclosed by alternating Taylor polynomials after exact
  reduction by quarter turns;
* square roots are enclosed by integer square root after dyadic scaling;
* the algebraic candidate h,s,t,d,q_* is enclosed directly from its exact
  defining radicals.

Its current self-test gives a rational enclosure of q_* of width below
4e-30 and proves, by exact rational arithmetic,

    q_* < 2.85118.

This suggests the final computer-assisted architecture: search the complement
of the already-proved local candidate neighborhood at the slightly larger
rational squared radius 2.85118. The local rigidity theorem proves the sharp
value q_* inside the neighborhood, while a rational interval certificate
excludes everything outside it. The final proof therefore need not compare
every search box directly with an irrational endpoint.


## Finite-certificate refinement

The current closure strategy has been sharpened in two ways.

### Rational search ceiling

The global finite cover does not need to represent the irrational candidate
value internally.  Put

[
 Q_0={142559over50000}=2.85118.
]

Using only

[
 {70710678over10^8}<1/sqrt2<{70710679over10^8}
]

and the defining quadratic for (s), exact rational arithmetic proves

[
 s<{84246over10^6},
 qquad
 q_*<Q_0.
]

More explicitly, for (r=84246/10^6),

[
p(r)=r^2-Ar+B<0,qquad r<A/2,
]

so (r) lies strictly between the two roots and the smaller root satisfies
(s<r).  Since (2s^2+4s+5/2) is increasing for positive (s),

[
q_*<2r^2+4r+5/2<Q_0.
]

Therefore it suffices for the finite verifier to exclude the complement of
the already-proved local candidate neighborhood under the slightly weaker
assumption (R^2le Q_0).  The local theorem handles the neighborhood at the
exact value (q_*).

`research/six/n6_exact_interval.py` checks these comparisons using
`fractions.Fraction` only.

### Exact cardinal cap contraction

For a unit square at acute frame deviation (	heta) from a chosen cardinal
normal, the sharp maximum cap depth at squared radius (Q_0) is

[
 B(	heta)=
 egin{cases}
  (ho_0-	frac12)cos	heta-	frac12sin	heta,
    &sqrt{Q_0}sin	hetale	frac12,\
  sqrt{Q_0}-cos	heta-sin	heta,
    &sqrt{Q_0}sin	hetage	frac12,
 end{cases}
]

where

[
 ho_0=sqrt{Q_0-	frac14}-	frac12.
]

The function is decreasing on ([0,pi/4]).  Thus a selected cardinal
separator gives a *bidirectional* contraction:

* the current side depth gives an upper bound on (	heta);
* the current lower bound on (	heta) gives a sharper central-coordinate
  bound.

This is substantially stronger than the earlier linear estimate.  For
example, the global central bound forces every cardinal helper to have acute
deviation below approximately (21.956^circ).  At (22.5^circ),

[
 B(pi/8)<3/2-ho_0,
]

so such a cardinal helper is already impossible.

The diagnostic verifier now applies this contraction iteratively.

### Discrete branch reduction

The globally forced cyclic type has two west-category squares, (W,D).
Since at most one exterior square can use any one central side, (W,D)
cannot both select the west cardinal separator.  Hence 8 of the nominal
32 central-separator patterns vanish immediately; 24 remain.

A diagnostic branch-8 run after adding the sharp cap contraction left only
7 depth-limit boxes in the first 30,000 visited boxes.  All seven had the
same alternate outer contact signature:

* (D-W) could separate only on (D)'s secondary axis;
* (D-S) could separate only on (S)'s secondary axis.

One further targeted split of each of those seven boxes made every child fail
either the global foot-type constraint or the selected central-separator
constraint.  This is useful evidence that those boxes were interval-dependency
artifacts, but it is **not** a statement that branch 8, or the full 24-pattern
cover, has been exhausted.

The next computational milestone is a complete fast cover whose terminal
boxes carry rule identifiers, followed by exact rational replay.


## Exact terminal certificate: alternate D--W axis

The first persistent diagnostic survivor family turned out to use a different
outer separator from the candidate: D--W separates on D's secondary axis
instead of W's near-vertical axis.

That family now has a fixed rational dual certificate. It uses only the five
separations C->N, S->C, W->N, D->W, and D->S, and ignores E completely.

The containment weights are

    (lambda_N,lambda_W,lambda_S,lambda_D)=(281,233,279,207)/1000,

and the separator multipliers are

    mu_CN=mu_SC=949/1000,
    mu_WN=277/1000, mu_DW=603/1000, mu_DS=738/1000.

For a fixed angle tuple, if m_i is the selected relative vertex and G_i is
the force induced by these five separator multipliers, weighted containment
and completion of squares give

    R^2 >= 1/2 + sum_e mu_e H_e
             - sum_i |2 lambda_i m_i-G_i|^2/(4 lambda_i).    (T)

The selected vertices are ++ for N, -+ for W, +- for S, and the lower
diamond vertex for D.

The exact replay in research/six/check_alt_dw_certificate.py proves
R^2 > Q0 = 2.85118 throughout

    |theta_N| <= 1/6, |theta_W| <= 2/5,
    1/6 <= theta_S <= 1/2, |eps_D| <= 1/6,

for either W or N supplying the W--N horizontal axis, provided C--N and
C--S use the common vertical axes, D--W uses D's secondary axis, and D--S
uses S's near-horizontal axis.

The replay uses fractions.Fraction only. Its transcendental inputs are the
standard alternating Taylor bounds for sine and cosine on [-3/4,3/4], plus
the exact rational enclosure

    70710678/10^8 < 1/sqrt(2) < 70710679/10^8.

The two source cases close after respectively 5110 and 3854 certified leaves,
at maximum subdivision depths 21 and 19.

This is the first nonlocal survivor family converted from a diagnostic search
observation into a compact exact terminal certificate.
