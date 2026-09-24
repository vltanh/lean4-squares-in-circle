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
