# Shared lemmas

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md)

This page is the toolkit shared by the cases. Each section defines its tools
and then proves the lemmas about them; the case pages cite both by number. The
setting (squares, packings, normal forms) is on the
[preliminaries page](preliminaries.md). Each result ends with the Lean
declarations it follows.

| section | definitions | lemmas | what it provides |
| --- | --- | --- | --- |
| [1. The disk centre seen from a square](#1-the-disk-centre-seen-from-a-square) | 6 to 8 | 1 | the disk constraint in terms of $(a_S, b_S)$ |
| [2. Contact polygons](#2-contact-polygons) | 9 to 11 | 2 | from the curved constraint to a polygon |
| [3. Two disjoint squares](#3-two-disjoint-squares) | 12 | 3 to 6 | inscribed disks, distance between centres, a separating line |
| [4. Arcs and the angular budget](#4-arcs-and-the-angular-budget) | 13, 14 | 7 to 9 | disjoint arcs share one circle |
| [5. Charts](#5-charts) | 15 | 10, 11 | a square in standard position as seen from $o$ |
| [6. Arcs of an exterior square](#6-arcs-of-an-exterior-square) | 16 | 12 to 14 | explicit arcs that an exterior square holds |
| [7. The radial sweep](#7-the-radial-sweep) | 17 | 15 to 18 | a longer arc for the square that contains $o$ |
| [8. Elementary estimates](#8-elementary-estimates) | | 19 | numerical bounds |
| [9. Axis-parallel squares](#9-axis-parallel-squares) | | 20 | checking the optimal packings |
| [10. Normal forms](#10-normal-forms) | | 21 to 23 | recognising the optimal packing |

## 1. The disk centre seen from a square

From here on the disk centre $o$ is fixed. Whether a square fits in a disk
about $o$ depends only on where $o$ lies relative to the square, and two
numbers record that.

### Definition 6 (position of the disk centre)

For a square $S$, let

```math
a_S = \max\left(|x_S(o)|, |y_S(o)|\right), \qquad b_S = \min\left(|x_S(o)|, |y_S(o)|\right),
```

the offsets of $o$ from $c_S$ along the two axes of $S$, larger first. A
quarter turn of the frame changes neither $S$
([Definition 1](preliminaries.md#definition-1-unit-square)) nor these two
numbers, and one of the four turns puts $o$ in the closed first quadrant. We
draw squares in that frame: there both local coordinates of $o$ are
nonnegative, and they are $a_S$ and $b_S$ in some order.

![A square in its own frame, with its centre c and the disk centre o outside it, up and to the right. A path goes from c along the first axis for a distance a, then parallel to the second axis for a distance b, reaching o](figures/position.svg)

*A square in its own frame, turned so that $o$ lies in the first quadrant.
From the centre $c_S$, the disk centre $o$ is $a_S$ along one axis and $b_S$
along the other.*

*Lean: [`alpha`](../../SquaresInCircles/Common/Basic.lean#L62),
[`beta`](../../SquaresInCircles/Common/Basic.lean#L63), the two offsets in the
order of the frame. Every statement is symmetric in them, and the proofs sort
them with
[`SquareChart.transfer`](../../SquaresInCircles/Common/Charts.lean#L94).*

### Definition 7 (containing and exterior squares)

A square $S$ is *containing* if $o \in S^\circ$, that is if $a_S < \frac12$,
and *exterior* otherwise. Two disjoint squares cannot both be containing, so a
packing has at most one containing square.

![Left: a tilted square with the disk centre o inside it, labelled containing, a_S less than one half. Right: a tilted square with o outside it, labelled exterior, a_S at least one half](figures/containing-exterior.svg)

*Left, $o$ lies in $S^\circ$ and $a_S < \frac12$. Right, $o$ lies outside
$S^\circ$ and $a_S \ge \frac12$.*

*Lean: [`openSquare`](../../SquaresInCircles/Geometry.lean#L36), applied to the
disk centre.*

### Definition 8 (farthest-vertex function)

For real numbers $a$ and $b$, let

```math
\varphi(a, b) = \left(a + \tfrac12\right)^2 + \left(b + \tfrac12\right)^2 .
```

For a square $S$, $\varphi(a_S, b_S)$ is the squared distance from $o$ to the
vertex of $S$ farthest from it
([Lemma 1](#lemma-1-farthest-vertex)).

*Lean: [`phi`](../../SquaresInCircles/Common/Basic.lean#L69).*

### Lemma 1 (farthest vertex)

For every square $S$, the vertex of $S$ farthest from $o$ is at squared
distance $\varphi(a_S, b_S)$ from $o$, and the centre is at squared distance
$a_S^2 + b_S^2$. In particular, if $\overline{S}$ lies in the closed disk of
radius $R$ about $o$, then

```math
\varphi(a_S, b_S) \le R^2 .
```

![The same square with a right triangle from o to the farthest vertex, the corner (-1/2, -1/2): a horizontal leg of length a plus one half, split where it crosses the vertical axis, a vertical leg of length b plus one half, split at the horizontal axis, and the hypotenuse of length the square root of phi(a, b)](figures/farthest-vertex.svg)

*The farthest vertex, $(-\frac12, -\frac12)$, is $a_S + \frac12$ across and
$b_S + \frac12$ down from $o$.*

*Proof.* Work in the frame of $S$ turned as in Definition 6 (figure above).
There $o = (x, y)$ with $x, y \ge 0$, and $x, y$ are $a_S, b_S$ in some
order. The vertices are $(\pm\frac12, \pm\frac12)$. The vertex
$(-\frac12, -\frac12)$, across both axes from $o$, is at squared distance
$(x + \frac12)^2 + (y + \frac12)^2 = \varphi(a_S, b_S)$, since $\varphi$ is
symmetric. No vertex is farther, because $|x \mp \frac12| \le x + \frac12$ and
$|y \mp \frac12| \le y + \frac12$. The centre is at squared distance
$x^2 + y^2 = a_S^2 + b_S^2$. $\square$

The proofs use the disk only through this inequality, one for each square.
Every lower bound and every uniqueness proof starts from these inequalities
and from then on works only with the pairs $(a_S, b_S)$ and the disjointness
of the squares.

*Lean: [`phi_le_of_contained`](../../SquaresInCircles/Common/Basic.lean#L81),
[`Packing.phi_le`](../../SquaresInCircles/Common/Basic.lean#L99),
[`local_center_norm`](../../SquaresInCircles/Common/Basic.lean#L178). The Lean
proof checks all four vertices instead of naming the far one.*

## 2. Contact polygons

By Lemma 1, a packing in a disk of radius $R$ has $\varphi(a_S, b_S) \le R^2$
for every square $S$. Plot each square $S$ as the point $(a_S, b_S)$ of an
auxiliary plane with coordinates $a$ and $b$, the $(a, b)$-plane; it is not the
plane the squares lie in. There the constraint is curved: $\varphi(a, b)$ is
the squared distance from $(a, b)$ to $(-\frac12, -\frac12)$, so
$\lbrace \varphi \le K \rbrace$ is a disk. The proofs replace it by a polygon
of tangent lines.

### Definition 9 (tangent half-plane)

Let $\varphi(u, v) = K$. The *tangent half-plane* at $(u, v)$ is the side of
the tangent line to $\lbrace \varphi = K \rbrace$ at $(u, v)$ that contains
the disk $\lbrace \varphi \le K \rbrace$:

```math
\left(u + \tfrac12\right)(a - u) + \left(v + \tfrac12\right)(b - v) \le 0 .
```

![The (a, b)-plane with the disk where phi is at most K, centred at (-1/2, -1/2), a point (u, v) on its boundary circle, and the tangent line there; the shaded side of the line, which contains the disk, is the tangent half-plane](figures/tangent-half-plane.svg)

*The disk $\lbrace \varphi \le K \rbrace$ is centred at $(-\frac12, -\frac12)$.
The tangent half-plane at a boundary point $(u, v)$ contains it.*

*Lean: written out in
[`tangent_le`](../../SquaresInCircles/Common/Tangents.lean#L20) and
[`tangent_lt`](../../SquaresInCircles/Common/Tangents.lean#L25).*

### Lemma 2 (tangent lines)

For all real $a, b, u, v$,

```math
\varphi(a,b) - \varphi(u,v) = 2\left(u+\tfrac12\right)(a-u) + 2\left(v+\tfrac12\right)(b-v) + (a-u)^2 + (b-v)^2 .
```

So if $\varphi(u, v) = K$ and $\varphi(a, b) \le K$, then $(a, b)$ lies in
the tangent half-plane at $(u, v)$, and strictly inside it if
$\varphi(a, b) < K$.

*Proof.* Expand. The last two terms are squares, hence nonnegative.
$\square$

*Lean: [`tangent_identity`](../../SquaresInCircles/Common/Tangents.lean#L15),
[`tangent_le`](../../SquaresInCircles/Common/Tangents.lean#L20),
[`tangent_lt`](../../SquaresInCircles/Common/Tangents.lean#L25).*

### Definition 10 (contact polygon)

A *contact polygon* is an intersection of a few tangent half-planes. Each case
takes $K$ to be the square of its optimal radius, and takes the tangent points
from its optimal packing, together with their mirror images. A point lies
*strictly* inside a polygon if every defining inequality is strict. The
polygons $P_3$, $P_4$ and $P_5$ of the individual cases are defined on their
pages.

*Lean: [`P3`](../../SquaresInCircles/Three/Tangents.lean#L12),
[`P4`](../../SquaresInCircles/Four/Tangents.lean#L12),
[`P5`](../../SquaresInCircles/Five/Tangents.lean#L12).*

### Definition 11 (the octagon)

One polygon serves two cases. The *octagon* $P_8$ is cut out by the tangents to
$\varphi = \frac52$ at $(1, 0)$ and $(0, 1)$:

```math
P_8:\qquad 3a + b \le 3, \qquad a + 3b \le 3 .
```

Restoring the signs and the order of the two local coordinates of $o$ turns
these two lines into eight, hence the name.

![The (a, b)-plane: the disk where phi is at most 5/2, inside the octagon P8 cut out by the tangents at (1, 0) and (0, 1); a dotted third tangent cuts off the octagon corner](figures/contact-polygon.svg)

*The disk $\lbrace \varphi \le \frac52 \rbrace$ and the octagon $P_8$ (its part
with $a, b \ge 0$), cut out by the tangents at $(1, 0)$ and $(0, 1)$. The dotted
third tangent cuts off the corner; five squares add it.*

*Lean: [`P8`](../../SquaresInCircles/Common/Tangents.lean#L30),
[`P8Strict`](../../SquaresInCircles/Common/Tangents.lean#L31).*

## 3. Two disjoint squares

### Lemma 3 (inscribed disks)

Let $S$ be a square.

1. The open disk of radius $\frac12$ about $c_S$ lies in $S^\circ$.
2. If $a_S \le \alpha$ and $b_S \le \alpha$ for some $\alpha < \frac12$, then
   the open disk of radius $\frac12 - \alpha$ about $o$ lies in $S^\circ$.

![A square with the dashed disk of radius one half about its centre c, and a smaller shaded disk of radius one half minus alpha about the point o](figures/inscribed-disks.svg)

*The disk of radius $\frac12$ about $c$, and the disk of radius
$\frac12 - \alpha$ about $o$, both inside $S$.*

*Proof.* (1) A point within $\frac12$ of $c_S$ has
$x_S^2 + y_S^2 < \frac14$, so both local coordinates are below $\frac12$ in
absolute value. (2) A point within $\frac12 - \alpha$ of $o$ has local
coordinates within $\frac12 - \alpha$ of those of $o$, which are at most
$\alpha$ in absolute value. $\square$

*Lean:
[`small_disk_in_openSquare`](../../SquaresInCircles/Common/Basic.lean#L159),
[`inscribed_disk_mem`](../../SquaresInCircles/Common/Coordinates.lean#L83).*

### Lemma 4 (centres at least 1 apart)

If $S$ and $T$ are disjoint, then $|c_T - c_S| \ge 1$.

![Two overlapping tilted squares whose centres are less than 1 apart, with their inscribed disks and the midpoint m of the centres lying in both](figures/midpoint.svg)

*If the centres were less than 1 apart, the midpoint $m$ would lie in both
inscribed disks.*

*Proof.* Otherwise the midpoint of the two centres is within $\frac12$ of
both, and by Lemma 3 (1) it lies in both open squares. $\square$

*Lean:
[`centers_distance_sq_ge_one`](../../SquaresInCircles/Common/Contacts.lean#L91).*

### Definition 12 (width)

For a square $S$ and a vector $n$,

```math
w_S(n) = \tfrac12\left(|\langle n, e^S_1\rangle| + |\langle n, e^S_2\rangle|\right) = \max_{p \in \overline{S}} \langle n,\ p - c_S\rangle ,
```

the half-width of $S$ in the direction $n$, measured in units of $|n|$.

![A tilted square, a unit direction n, and the distance from the centre c to the supporting line through the extreme vertex in that direction](figures/width.svg)

*For a unit vector $n$, the square reaches $w_S(n)$ beyond its centre in the
direction $n$.*

*Lean: [`width`](../../SquaresInCircles/Common/Separation.lean#L67).*

### Lemma 5 (supporting line)

Let $S$ and $T$ be disjoint.

1. There is a vector $n \ne 0$ with

   ```math
   w_S(n) + w_T(n) \le \langle n,\ c_T - c_S\rangle .
   ```

   In words: some line separates the two squares, and each square lies
   entirely on its own side.
2. No point of the closed square $\overline{S}$ lies in $T^\circ$.

![Two disjoint tilted squares, a dashed separating line between them, and their shadows on a line in direction n, which do not overlap](figures/shadows.svg)

*Disjoint squares have disjoint shadows in some direction $n$. Each shadow
reaches $w(n)$ on either side of the shadow of the centre.*

*Idea.* Hahn–Banach gives a separating line. Pushing test points out to the
vertices of each square shows that the line clears both squares by their full
half-widths.

*Proof.* The open squares are disjoint, open and convex, so the geometric
Hahn–Banach theorem gives a nonzero $n$ and a number $\kappa$ with

```math
\langle n, p\rangle < \kappa < \langle n, q\rangle \qquad \text{for all } p \in S^\circ,\ q \in T^\circ .
```

Fix $0 \le t < 1$. Go from $c_S$ a fraction $t$ of the way to the vertex of
$S$ that maximises $\langle n, \cdot\rangle$: this point is in $S^\circ$ and
has value $\langle n, c_S\rangle + t w_S(n)$. Do the same in $T$ with $-n$.
Then

```math
\langle n, c_S\rangle + t\,w_S(n) < \langle n, c_T\rangle - t\,w_T(n)
\qquad \text{for every } 0 \le t < 1,
```

and letting $t \to 1$ proves (1). For (2), every $p \in \overline{S}$ and
$q \in T^\circ$ satisfy

```math
\langle n, p\rangle \le \langle n, c_S\rangle + w_S(n) \le \langle n, c_T\rangle - w_T(n) < \langle n, q\rangle . \qquad \square
```

*Lean:
[`support_separator`](../../SquaresInCircles/Common/Separation.lean#L134),
[`closed_dot_bound`](../../SquaresInCircles/Common/Support.lean#L166),
[`closed_open_disjoint`](../../SquaresInCircles/Common/Support.lean#L177),
[`support_point`](../../SquaresInCircles/Common/Separation.lean#L83),
[`bound_from_shrinks`](../../SquaresInCircles/Common/Separation.lean#L109).*

### Lemma 6 (squares at distance 1)

If $S$ and $T$ are disjoint and $|c_T - c_S| = 1$, then $T$ has its sides
parallel to those of $S$ and shares a full edge with it: $c_T - c_S$ is one of
$\pm e^S_1, \pm e^S_2$.

![Two tilted squares sharing a full edge, with their centres joined by a segment of length 1](figures/edge-contact.svg)

*At distance exactly 1 the squares share a full edge.*

*Idea.* At distance exactly 1 every inequality in the separation argument
must be tight, and tightness pins down the directions.

*Proof.* Take $n$ from Lemma 5 and put $d = c_T - c_S$, a unit vector. Since
$|\langle n, e^S_1\rangle| + |\langle n, e^S_2\rangle| \ge |n|$, and the same
for $T$, each width is at least $|n|/2$. Therefore

```math
|n| \le w_S(n) + w_T(n) \le \langle n, d\rangle \le |n|\,|d| = |n| ,
```

and all three inequalities are equalities.

- The last one is Cauchy–Schwarz, so $n$ is a positive multiple of $d$.
- The first one forces $|\langle n, e^S_1\rangle| + |\langle n, e^S_2\rangle| = |n|$,
  and the same for $T$, which happens only when $n$ is parallel to a side.

So $d$ is parallel to a side of $S$ and to a side of $T$. $\square$

*Lean: [`unit_contact`](../../SquaresInCircles/Common/Contacts.lean#L118).*

## 4. Arcs and the angular budget

The main tool for three to five squares measures how much of a small circle
about $o$ each square covers. Disjoint squares cover disjoint parts of the
circle, and together they cannot cover more than all of it.

### Definition 13 (circles about the disk centre)

For $r > 0$, the circle of radius $r$ about $o$ is

```math
\Gamma_r = \lbrace o + r\,u(\theta) \rbrace ,
```

with its points labelled by directions. The *angle* $d(\theta, \theta')$
between two directions is their distance on the circle of directions, a number
in $[0, \pi]$.

![Two directions from o drawn as radii of the circle of radius r, the unit vector u(theta), and the angle d between the two directions](figures/directions.svg)

*Two directions $\theta, \theta'$ seen from $o$, the unit vector $u(\theta)$,
and the angle $d(\theta, \theta')$ between them.*

*Lean: [`circlePoint`](../../SquaresInCircles/Common/AngularBudget.lean#L22),
[`direction_dist`](../../SquaresInCircles/Common/AngularBudget.lean#L31).*

### Definition 14 (arc)

Let $U$ be a set in the plane. An *arc of $U$ on $\Gamma_r$*, with centre
$\theta_0$ and half-width $w \in (0, \pi]$, says that every point
$o + r u(\theta)$ with $d(\theta, \theta_0) < w$ lies in $U$. The arc need not
be all of $\Gamma_r \cap U$. When $U$ is an open square $S^\circ$, we say that
$S$ *holds* the arc.

![A circle about o and a square U; a thick arc of the circle inside U with centre direction theta zero and half-width w, and the rest of the circle inside U drawn thin](figures/arc.svg)

*An arc of $U$ with centre $\theta_0$ and half-width $w$ (thick). It need not
cover all of $\Gamma_r \cap U$ (thin).*

*Lean: [`OpenArc`](../../SquaresInCircles/Common/AngularBudget.lean#L39).*

![Four disjoint squares around the disk centre, each holding a coloured arc of the circle of radius r; the arcs do not overlap](figures/budget.svg)

*Disjoint squares hold disjoint arcs of the same circle, so the arcs
share its $2\pi$ of angle.*

### Lemma 7 (angular budget)

If the sets $U_1, \dots, U_n$ are pairwise disjoint and $U_i$ holds an arc of
half-width $w_i$ on a common circle $\Gamma_r$, then

```math
w_1 + \dots + w_n \le \pi .
```

In particular it cannot happen that every $w_i \ge \pi/n$ and one of them is
strictly larger.

*Proof.* Fix $0 \le t < 1$ and shrink every arc to half-width $t w_i$, closed.
The shrunk arcs are still pairwise disjoint, since a common direction would
put one point of $\Gamma_r$ in two of the $U_i$. Their lengths $2t w_i$ add
up to at most $2\pi$, the total length of the circle. So $t \sum w_i \le \pi$
for every $t < 1$. $\square$

Shrinking first means the proof never has to measure the endpoints of an open
arc.

*Lean:
[`open_arc_budget`](../../SquaresInCircles/Common/AngularBudget.lean#L81),
[`closed_arc_budget`](../../SquaresInCircles/Common/AngularBudget.lean#L49),
[`uniform_arc_excess`](../../SquaresInCircles/Common/AngularBudget.lean#L114).
The length is the Haar measure on $\mathbb{R}/2\pi\mathbb{Z}$.*

### Lemma 8 (disjoint arcs have separated centres)

If disjoint sets $U$ and $V$ hold arcs on the same circle with centres
$\theta_U, \theta_V$ and half-widths $w_U, w_V$, then

```math
d(\theta_U, \theta_V) \ge w_U + w_V .
```

![Two disjoint arcs U and V of a circle about o, with dashed radii to their centres and the angle between the centres marked as at least w_U + w_V](figures/arc-centres.svg)

*The centres of two disjoint arcs are at least $w_U + w_V$ apart.*

*Proof.* Suppose $d(\theta_U, \theta_V) < w_U + w_V$, and walk from
$\theta_U$ towards $\theta_V$ a fraction $\frac{w_U}{w_U + w_V}$ of the way.
The direction reached is less than $w_U$ from $\theta_U$ and less than $w_V$
from $\theta_V$, so its point on the circle lies in $U$ and in $V$. $\square$

*Lean:
[`OpenArc.centers_separated`](../../SquaresInCircles/Common/ArcMetric.lean#L25).*

### Lemma 9 (three arcs)

If pairwise disjoint sets $U, V, W$ hold arcs on the same circle with centres
$\theta_U, \theta_V, \theta_W$ and half-widths $w_U, w_V, w_W$, then

```math
w_V + w_W \le d(\theta_V, \theta_W) \le 2\pi - 2w_U - w_V - w_W ,
```

and in particular $w_U + w_V + w_W \le \pi$.

![A circle about o with three disjoint coloured arcs U, V and W, dashed radii to their centres, and the angle between the centres of V and W marked](figures/three-arcs.svg)

*The short way from $\theta_V$ to $\theta_W$ crosses half of $V$ and half of
$W$. The long way crosses those halves and all of $U$.*

*Proof.* Three points on a circle of length $2\pi$ have pairwise distances
adding up to at most $2\pi$. Bound $d(\theta_U, \theta_V)$ and
$d(\theta_U, \theta_W)$ from below by Lemma 8. $\square$

This gives the budget for three sets without measure theory, and it also
locates the centres, which the uniqueness proofs use.

*Lean:
[`OpenArc.third_distance_bounds`](../../SquaresInCircles/Common/ArcMetric.lean#L112),
[`triple_arc_budget`](../../SquaresInCircles/Common/ArcMetric.lean#L125),
[`direction_triangle_perimeter`](../../SquaresInCircles/Common/ArcMetric.lean#L87).*

## 5. Charts

To find the arcs that a square holds, turn the picture about $o$, and reflect
it if needed, until the square sits in a standard position.

### Definition 15 (chart)

A *chart* of $S$ is a direction $\theta_S$ (the *phase*) and a sign
$\varepsilon_S = \pm 1$ such that for all real $r, t, m$

```math
o + r\,u(\theta_S + \varepsilon_S t) - m\,(c_S - o) \in S^\circ
\iff
\left|r\cos t - (1+m)a_S\right| < \tfrac12 \ \text{ and } \ \left|r\sin t - (1+m)b_S\right| < \tfrac12 .
```

Take $m = 0$ first. The condition says: measure angles from $o$ as
$\theta_S + \varepsilon_S t$ and use $t$ as the angle variable (the *chart
angle*); then $S$ is the axis-parallel unit square centred at $(a_S, b_S)$.
The parameter $m$ slides $S$ away from $o$ along the ray through its centre,
and moves the centre to $(1 + m)(a_S, b_S)$.
Lemma 10 below shows that every square has a chart.

![Left: a tilted square seen from o, with the phase direction and a point on the circle at chart angle t from it. Right: the same square turned into standard position, centred at (a, b), with the point at angle t](figures/chart-panels.svg)

*Left: a square seen from $o$. Right: its chart. Turning by $-\theta_S$ (and
reflecting when $\varepsilon_S = -1$) puts the square in standard position,
centred at $(a_S, b_S)$; the point at angle $\theta_S + \varepsilon_S t$ goes
to the point at chart angle $t$.*

*Lean: [`SquareChart`](../../SquaresInCircles/Common/Charts.lean#L69),
[`chartAngle`](../../SquaresInCircles/Common/Charts.lean#L66).*

### Lemma 10 (charts)

Every square $S$ has a chart $(\theta_S, \varepsilon_S)$, and:

1. $o \in S^\circ$ exactly when $a_S < \frac12$; an exterior square has
   $a_S \ge \frac12$.
2. Suppose every chart angle $t$ in an interval $(l, h)$ of length at most
   $2\pi$ gives a point of $S$ on $\Gamma_r$, that is
   $|r\cos t - a_S| < \frac12$ and $|r\sin t - b_S| < \frac12$. Then $S$
   holds an arc of $\Gamma_r$ with half-width $\frac{h - l}2$ and centre
   $\theta_S + \varepsilon_S\frac{l + h}2$.

*Idea.* Rotate so that an axis of $S$ points along $\theta_S$, then reflect
so that the centre of $S$ lands at $(a_S, b_S)$.

*Proof.* Let $\theta$ be the direction of $e^S_1$ and write
$c_S - o = X e^S_1 + Y e^S_2$. The point $o + r u(\theta + s)$ has local
coordinates $(r\cos s - X, r\sin s - Y)$, and sliding by $-m(c_S - o)$
subtracts a further $m(X, Y)$.

- Suppose $|X| \ge |Y|$, so that $|X| = a_S$ and $|Y| = b_S$. If
  $X, Y \ge 0$, the chart $(\theta, 1)$ works with $s = t$. If
  $Y < 0 \le X$, substitute $s = -t$; if $X < 0 \le Y$, substitute
  $s = \pi - t$; if both are negative, substitute $s = \pi + t$. Each flips
  the signs that need flipping.
- If $|X| < |Y|$, do the same with the two axes exchanged: turning the phase
  by a quarter turn and substituting $t \mapsto \frac\pi2 - t$ exchanges
  cosine and sine, and flips the orientation.

Part 1 is the chart condition at $r = m = 0$, since $b_S \le a_S$. Part 2
holds because the directions within $\frac{h - l}2$ of
$\theta_S + \varepsilon_S\frac{l + h}2$ are exactly the
$\theta_S + \varepsilon_S t$ with $t \in (l, h)$. $\square$

*Lean: [`square_chart`](../../SquaresInCircles/Common/Charts.lean#L110),
[`sorted_square_chart`](../../SquaresInCircles/Common/Charts.lean#L175),
[`SquareChart.origin`](../../SquaresInCircles/Common/Charts.lean#L182),
[`SquareChart.exterior`](../../SquaresInCircles/Common/Charts.lean#L188),
[`SquareChart.arc`](../../SquaresInCircles/Common/Charts.lean#L212).*

### Lemma 11 (Cartesian form of a chart)

If $(\theta_S, \varepsilon_S)$ is a chart of $S$, then $S$ sits at
$(a_S, \varepsilon_S b_S)$ in the frame $\theta_S$.

*Proof.* Write a point in polar form $(r\cos t, r\sin t)$ in the frame
$\theta_S$ and apply the chart condition with $m = 0$, replacing $t$ by $-t$
when $\varepsilon_S = -1$. $\square$

*Lean:
[`SquareChart.cartesian`](../../SquaresInCircles/Common/Coordinates.lean#L42),
[`chart_represents`](../../SquaresInCircles/Common/NormalForm.lean#L175).*

## 6. Arcs of an exterior square

Throughout this section $S$ is exterior, so $a_S \ge \frac12$, and $\Gamma_r$
is a circle about $o$.

### Definition 16 (cap angles)

Let $S$ be exterior, so $a_S \ge \frac12$, and let $r > 0$. Put

```math
A_S = \arccos\frac{a_S - \frac12}{r}, \qquad V_S = \arcsin\frac{\frac12 - b_S}{r} .
```

In the chart, the circle $\Gamma_r$ crosses the line of the near edge,
$x = a_S - \frac12$, at the chart angles $\pm A_S$, and the line of the lower
edge, $y = b_S - \frac12$, at $-V_S$. The radius $r$ is fixed by context and
left out of the notation.

![An exterior square in its chart. The disk centre o is at the origin and the square is centred at (a, b). The circle of radius r crosses the dashed line of the near edge at the angles plus and minus A, and the dashed line of the lower edge at minus V. The cap, the part of the circle inside the square, is highlighted from minus V to A](figures/chart.svg)

*An exterior square in its chart, with $o$ at the origin. The circle
$\Gamma_r$ crosses the line of the near edge at the angles $\pm A_S$ and the
line of the lower edge at $-V_S$. The cap is the part of the circle inside the
square. Here $V_S < A_S$, so the lower edge clips it and it runs from $-V_S$
to $A_S$; when $A_S \le V_S$ it runs from $-A_S$ to $A_S$.*

*Lean: [`threeCapA`](../../SquaresInCircles/Three/Exterior.lean#L21),
[`threeCapV`](../../SquaresInCircles/Three/Exterior.lean#L22) (for
$r = \frac38$; written out in the other cases).*

### Lemma 12 (occupied interval)

Suppose $r < a_S + \frac12$ and $0 \le \frac{a_S - 1/2}{r} \le 1$. Then every chart
angle $t$ with

```math
\max\left(-A_S,\ \arcsin\frac{b_S - \frac12}{r}\right) < t < \min\left(A_S,\ \arcsin\frac{b_S + \frac12}{r}\right)
```

gives a point of the square on $\Gamma_r$.

*Proof.* The bound $|t| < A_S$ keeps the point beyond the near edge:
$r\cos t > r\cos A_S = a_S - \frac12$. The far edge is out of reach:
$r\cos t \le r < a_S + \frac12$. The two arcsine bounds keep it between the
lower and upper edges, because the sine increases on
$[-\frac\pi2, \frac\pi2]$. $\square$

*Lean: [`cap_mem`](../../SquaresInCircles/Common/RectangleArcs.lean#L48).*

### Lemma 13 (the cap)

Suppose $r \le \frac12$, $a_S - \frac12 < r$ and $b_S \le \frac12$. Then $S$ holds
an arc of $\Gamma_r$ of length

```math
\min(2A_S,\ A_S + V_S) ,
```

called the *cap*. If $A_S \le V_S$ the cap is symmetric: it runs from $-A_S$ to $A_S$
and is centred at the phase $\theta_S$. If $V_S < A_S$ the lower edge clips it,
and it runs from $-V_S$ to $A_S$.

*Proof.* The circle is too small to reach the upper edge, since
$b_S + \frac12 \ge \frac12 \ge r$. So the interval of Lemma 12 is
$(\max(-A_S, -V_S), A_S)$, whose length is $\min(2A_S, A_S + V_S)$, and Lemma 10 (2)
turns it into an arc. $\square$

*Lean:
[`SquareChart.cap_arc`](../../SquaresInCircles/Common/RectangleArcs.lean#L89),
[`cap_mem_near`](../../SquaresInCircles/Common/RectangleArcs.lean#L74),
[`cap_length_identity`](../../SquaresInCircles/Common/RectangleArcs.lean#L39).*

### Lemma 14 (the rectangle interval)

Suppose $r < a_S + \frac12$, $0 \le \frac{a_S - 1/2}{r} < 1$, and the near corner
$(a_S - \frac12, b_S - \frac12)$ lies strictly inside the circle of radius $r$.
Then $S$ holds an arc of $\Gamma_r$ of every length below

```math
\min\left(A_S,\ \arcsin\frac{b_S + \frac12}{r}\right) - \arcsin\frac{b_S - \frac12}{r} .
```

This interval can reach past the far side of the cap; five squares use it on a
larger circle.

![An exterior square in its chart with a circle of radius 5/6 about o; the highlighted arc runs from where the circle crosses the lower edge to where it crosses the upper edge, before the near edge](figures/rectangle-interval.svg)

*On a larger circle the arc can leave through the upper edge. Here it runs from
the lower edge to the upper edge, which the circle meets before the near edge
(grey dot).*

*Proof.* By Lemmas 12 and 10 (2), it suffices to show
$-A_S < \arcsin\frac{b_S - 1/2}{r}$: going clockwise, the circle leaves the square
through the lower edge before it reaches the line of the near edge. Put
$p = \frac{a_S - 1/2}{r}$ and $q = \frac{b_S - 1/2}{r}$. If $q \ge 0$ there is
nothing to prove. Otherwise $p^2 + q^2 < 1$ gives
$-q < \sqrt{1 - p^2} = \cos(\arcsin p)$, so
$\arcsin(-q) < \frac\pi2 - \arcsin p = A_S$. $\square$

*Lean:
[`exterior_arc_from_length`](../../SquaresInCircles/Common/RectangleArcs.lean#L118),
[`near_corner_angle`](../../SquaresInCircles/Common/RectangleArcs.lean#L12).*

## 7. The radial sweep

The square that contains $o$, if there is one, may hold only a short arc of
the auxiliary circle. Four and five squares enlarge it.

### Definition 17 (radial sweep)

The *radial sweep* of a square $S$ is

```math
\widehat{S} = \bigcup_{m \ge 0} \left( S^\circ + m\,(c_S - o) \right),
```

the region that $S^\circ$ covers as it slides away from $o$ along the ray
through its centre.

![A square containing the disk centre that does not reach the circle of radius r. Dotted copies of it slid away from the centre along the ray through its centre fill the radial sweep, which covers a long highlighted arc of the circle](figures/sweep.svg)

*The square $S$ contains $o$ but does not reach the circle
$\Gamma_r$. Sliding it away from $o$ along the ray through its centre (dotted
copies) sweeps out $\widehat{S}$, which covers the highlighted arc. Five
squares use exactly this
([Lemma 5.7](five.md#lemma-57-the-sweep-holds-a-fifth-of-the-circle)).*

*Lean: [`openRay`](../../SquaresInCircles/Common/Support.lean#L77).*

The sweep holds longer arcs than the square itself. The lemmas below show that
it still avoids every other square, as long as every square $S$ has
$(a_S, b_S)$ in the octagon $P_8$.

### Lemma 15 (octagon support)

1. If $a, b \ge 0$, $(a, b) \in P_8$ and $p, q \ge 0$, then

   ```math
   pa + qb \le \max\left(p,\ q,\ \tfrac34(p+q)\right) ,
   ```

   strictly if $(a, b)$ is strictly in $P_8$ and $p + q > 0$.
2. For any two squares $S, T$ and any vector $n$, with
   $p = |\langle n, e_1^S\rangle|$ and $q = |\langle n, e_2^S\rangle|$,

   ```math
   \max\left(p,\ q,\ \tfrac34(p+q)\right) \le w_S(n) + w_T(n) .
   ```

![The quadrilateral with vertices (0, 0), (1, 0), (3/4, 3/4) and (0, 1), dashed level lines of pa + qb, and the level line through the corner (3/4, 3/4), where the largest value is reached](figures/octagon-support.svg)

*Part (1): over the quadrilateral, $pa + qb$ is largest at a vertex, here
$(\frac34, \frac34)$.*

*Proof.* (1) The region $a, b \ge 0$ inside $P_8$ is the quadrilateral with
vertices $(0,0)$, $(1,0)$, $(\frac34, \frac34)$, $(0,1)$, and $pa + qb$ is
largest at a vertex. Explicitly: if $p \ge 3q$, then
$pa + qb \le \frac p3(3a + b) \le p$; the case $q \ge 3p$ is symmetric;
otherwise both weights below are nonnegative and

```math
pa + qb = \frac{3p - q}{8}(3a + b) + \frac{3q - p}{8}(a + 3b) \le \frac34(p + q) .
```

(2) Let $u, v$ be the absolute components of $n$ in the frame of $T$, so that
$w_S(n) + w_T(n) = \frac{p+q}2 + \frac{u+v}2$. Since
$p^2 + q^2 = u^2 + v^2 = |n|^2$, each of $p$ and $q$ is at most
$|n| \le u + v$. That gives $p \le \frac{p+q}2 + \frac{u+v}2$, the same for
$q$, and $\frac34(p+q) \le \frac{p+q}2 + \frac{u+v}2$ because
$\frac{p+q}2 \le u + v$. $\square$

*Lean: [`octagon_linear_le`](../../SquaresInCircles/Common/Support.lean#L18),
[`octagon_linear_lt`](../../SquaresInCircles/Common/Support.lean#L38),
[`octSupport_le_widths`](../../SquaresInCircles/Common/Support.lean#L91).*

### Lemma 16 (the sweep is safe)

If $S$ and $T$ are disjoint and $(a_S, b_S)$ and $(a_T, b_T)$ both lie in
$P_8$, then the sweep $\widehat{S}$ does not meet $T^\circ$.

![Two disjoint squares S and T, a dashed separating line between them with n pointing towards T, and the radial sweep of S extending away from T along the ray from o through its centre](figures/safe-sweep.svg)

*The separating line between $S$ and $T$, with $n$ pointing towards $T$. The ray
from $o$ through $c_S$ points away from $T$, so the sweep of $S$ stays on its
side.*

*Idea.* Take the separating line of Lemma 5. The octagon forces the ray from
$o$ through $c_S$ to point away from $T$ across that line, so sliding $S$
along the ray only moves it further from $T$.

*Proof.* Take $n$ from Lemma 5 and write $W = w_S(n) + w_T(n)$.

1. *Where $o$ lies.* In the frame of $S$, the coordinates of $c_S - o$ are
   $\pm a_S$ and $\pm b_S$ in some order. Lemma 15 is symmetric in $p$ and
   $q$, so it gives $|\langle n, c_S - o\rangle| \le W$,
   and in the same way $|\langle n, c_T - o\rangle| \le W$. The difference of
   the two is $\langle n, c_T - c_S\rangle \ge W$, which forces

   ```math
   \langle n,\ c_S - o\rangle \le 0 \le \langle n,\ c_T - o\rangle .
   ```

2. *Sliding.* For $q \in S^\circ$, $m \ge 0$ and $p \in T^\circ$,

   ```math
   \langle n,\ q + m(c_S - o)\rangle \le \langle n, q\rangle < \langle n, c_S\rangle + w_S(n)
   \le \langle n, c_T\rangle - w_T(n) < \langle n, p\rangle ,
   ```

   so no point of the sweep lies in $T^\circ$. $\square$

*Lean:
[`safe_openRay_of_disjoint`](../../SquaresInCircles/Common/Support.lean#L139),
[`Separation.center_signs`](../../SquaresInCircles/Common/Support.lean#L116).*

### Lemma 17 (no centred square)

If $S$ and $T$ are disjoint and $(a_T, b_T)$ is strictly inside $P_8$, then
$c_S \ne o$.

*Proof.* As in the previous proof, and now strictly by Lemma 15,
$|\langle n, c_T - o\rangle| < W$. If $c_S = o$ this contradicts
$\langle n, c_T - c_S\rangle \ge W$. $\square$

*Lean:
[`center_ne_of_strict_octagon`](../../SquaresInCircles/Common/Support.lean#L156).*

### Proposition 18 (budget with a sweep)

Let $n \ge 2$ pairwise disjoint squares all have $(a_S, b_S) \in P_8$, and fix
a circle $\Gamma_r$. The following cannot both hold:

- the sweep of the containing square, if there is one, holds an arc of
  half-width at least $\pi/n$;
- every exterior square holds an arc of half-width more than $\pi/n$.

*Proof.* Replace the containing square by its sweep. By Lemma 16 the $n$ sets
are still pairwise disjoint. At most one square contains $o$, so with $n \ge 2$
some square is exterior and gives the strict inequality that Lemma 7 needs.
$\square$

*Lean:
[`ray_budget_impossible`](../../SquaresInCircles/Common/Regions.lean#L40),
[`rayRegions_disjoint`](../../SquaresInCircles/Common/Regions.lean#L23).*

## 8. Elementary estimates

### Lemma 19 (elementary estimates)

1. $\pi < \frac{22}7$.
2. $\arcsin x \ge x$ for $0 \le x \le 1$.
3. $\arcsin x \le x + \frac{x^3}4$ for $0 \le x \le \frac35$.
4. If $0 \le \theta \le \frac\pi2$, $u, v \in [0, 1]$ and
   $\sin\theta < \frac{u+v}2$, then $2\theta < \arcsin u + \arcsin v$.
5. $\cos t > \frac{401}{500}$ for $|t| \le \frac\pi5$, and
   $\sin\frac\pi5 < \frac35$.

*Proof.*

1. This is mathlib's bound $\pi < 3.1416$.
2. $\sin y \le y$ for $y \ge 0$.
3. Put $y = x + \frac{x^3}4$; then $y \le \frac{109}{100}x$, and
   $\sin y > y - \frac{y^3}6 \ge x$.
4. Let $\mu$ and $\delta$ be the half-sum and half-difference of the two
   arcsines. Then $\frac{u+v}2 = \sin\mu\cos\delta \le \sin\mu$, so
   $\sin\theta < \sin\mu$ and $\theta < \mu$.
5. $\cos t \ge 1 - \frac{t^2}2$ and $|t| < \frac{22}{35}$. Then
   $\sin^2\frac\pi5 < 1 - (\frac{401}{500})^2 < \frac9{25}$. $\square$

*Lean:
[`pi_lt_22_over_7`](../../SquaresInCircles/Common/ElementaryTrig.lean#L16),
[`arcsin_ge_self`](../../SquaresInCircles/Common/ElementaryTrig.lean#L19),
[`arcsin_le_cubic`](../../SquaresInCircles/Common/ElementaryTrig.lean#L31),
[`arcsin_sum_gt_of_sin_lt`](../../SquaresInCircles/Common/ElementaryTrig.lean#L56),
[`cos_gt_401_500`](../../SquaresInCircles/Common/ElementaryTrig.lean#L94),
[`sin_pi_fifth_lt_three_fifths`](../../SquaresInCircles/Common/ElementaryTrig.lean#L102).*

## 9. Axis-parallel squares

### Lemma 20 (axis-parallel squares)

1. $Q(p)$ and $Q(q)$ are disjoint as soon as $p$ and $q$ differ by at least 1
   in one coordinate.
2. $\overline{Q(c)}$ lies in the closed disk of radius $R$ about the origin as
   soon as it lies in a box $[-B, B] \times [-C, C]$ with $B^2 + C^2 \le R^2$.

![Two axis-parallel squares Q(p) and Q(q), inside a box of half-sides B and C centred at the origin, inside the dashed circle of radius root of B squared plus C squared](figures/axis-squares.svg)

*The box $[-B, B] \times [-C, C]$ lies in the disk of radius $\sqrt{B^2 + C^2}$,
which passes through its corners.*

*Proof.* Two open unit intervals with centres at least 1 apart are disjoint.
Every point of the box is within $\sqrt{B^2 + C^2}$ of the origin. $\square$

*Lean: [`axis_disjoint`](../../SquaresInCircles/Common/Constructions.lean#L22),
[`axis_contained`](../../SquaresInCircles/Common/Constructions.lean#L31).*

## 10. Normal forms

Each uniqueness proof ends the same way: find one frame at $o$ in which every
square sits at a model centre
([Definition 4](preliminaries.md#definition-4-frames-at-the-disk-centre)), then
apply Lemma 22.

### Lemma 21 (sitting at a centre)

1. Let $\phi$ be the direction of $e_1^S$. In the frame $\phi$, $S$ sits at the
   coordinates of $c_S - o$ in the frame of $S$. So does every square $T$ with
   sides parallel to those of $S$, at the coordinates of $c_T - o$.
2. If $S$ sits at $c$ in the frame $\phi + k\frac\pi2$, then in the frame
   $\phi$ it sits at $c$ turned by $k$ quarter turns.

![A square S and a square T with the same axes, and dashed axes at o parallel to their sides; a path from o along the first axis for c1, then along the second for c2, reaches the centre of T](figures/parallel-squares.svg)

*Part (1): in the frame at $o$ parallel to the sides of $S$, the square $T$ sits
at the coordinates $(c_1, c_2)$ of $c_T - o$.*

*Proof.* (1) In the frame $\phi$, the local coordinates of $T$ are the frame
coordinates minus those of $c_T - o$, possibly turned by a multiple of a
quarter turn, and a quarter turn maps the open square $(-\frac12, \frac12)^2$
to itself. (2) Turning the frame by $k\frac\pi2$ turns all coordinates by the
same angle. $\square$

*Lean: [`self_represents`](../../SquaresInCircles/Common/Contacts.lean#L84),
[`same_axes_represents`](../../SquaresInCircles/Common/Contacts.lean#L63),
[`represents_quarter`](../../SquaresInCircles/Common/Angles.lean#L33).*

### Lemma 22 (from slots to a normal form)

If the squares $S_1, \dots, S_n$ of a packing are pairwise disjoint and each
one sits at one of the points $c_1, \dots, c_n$ in a common frame $\phi$, then
the packing has the normal form of $c_1, \dots, c_n$.

*Proof.* Two squares that sit at the same $c_j$ would both contain the point
$F_\phi(c_j)$, so the squares take different slots; with $n$ squares and $n$
slots, the assignment is a relabelling. The closed squares follow, since a
closed square is the closure of the open one. $\square$

*Lean:
[`normal_form_of_slots`](../../SquaresInCircles/Common/NormalForm.lean#L145),
[`same_open_same_closed`](../../SquaresInCircles/Common/NormalForm.lean#L80).
Lean reaches a boundary point along the segment from the centre instead of
taking a closure.*

### Lemma 23 (four directions)

Four directions at pairwise distance at least $\frac\pi2$ are
$\theta_0 + k\frac\pi2$ for $k = 0, 1, 2, 3$, in some order.

![Four radii of a circle about o in the directions theta0, theta0 plus pi/2, theta0 plus pi and theta0 plus 3pi/2](figures/four-directions.svg)

*Four directions pairwise at least $\frac\pi2$ apart: the only way is a quarter
grid.*

*Proof.* Write the other three as $\theta_0 + t_i$ with $t_i \in (-\pi, \pi]$,
sorted as $x \le y \le z$. Each has absolute value at least $\frac\pi2$,
consecutive ones differ by at least $\frac\pi2$, and $z - x \le \frac{3\pi}2$
because $\theta_0 + x$ and $\theta_0 + z$ are also $\frac\pi2$ apart going
the other way round.

- If $y < 0$, then $y \le -\frac\pi2$ and $x \le -\pi$, which is impossible.
- So $y \ge \frac\pi2$ and $z \ge \pi$, hence $z = \pi$ and $y = \frac\pi2$.
- Then $x \le 0$ forces $x \le -\frac\pi2$, and $z - x \le \frac{3\pi}2$
  forces $x = -\frac\pi2$. $\square$

*Lean: [`four_directions_grid`](../../SquaresInCircles/Common/Angles.lean#L64).*