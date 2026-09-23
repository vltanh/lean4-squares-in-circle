# Five squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 5.** Let $R_5 = \sqrt{5/2}$, and let $c_1, \dots, c_5$ be the points
$(0, 0)$, $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$.

1. $Q(c_1), \dots, Q(c_5)$ form a packing in the closed disk of radius $R_5$
   about the origin: the plus, one square centred at the disk centre and its
   four side-neighbours.
2. A packing of five unit squares in a closed disk of radius $R$ forces
   $R \ge R_5$.
3. A packing of five unit squares in a closed disk of radius $R_5$ has the
   normal form of $c_1, \dots, c_5$.

![The plus in its dashed circle of radius root of 5/2, with the circle of radius 5/6 about the centre; each outer square holds a coloured arc of about 74 degrees, and the grey centre square holds none](figures/five.svg)

*The plus. Each outer square holds an arc of about 74° of the
circle $\Gamma_{5/6}$; the centre square (grey) holds none.*

*Sketch.* Draw the circle $\Gamma_{5/6}$ about the disk centre. In a disk of
radius at most $R_5$, every square that avoids the centre holds more than a
fifth of it, and the radial sweep of a square containing the centre holds a
fifth, unless that square is centred exactly at the disk centre. Five such
arcs do not fit, so some square is centred at the disk centre. In a smaller
disk that is impossible. At radius $R_5$ the other four squares are then at
distance exactly 1 from it: the plus.

Unlike three and four squares, the arc argument here needs only the closed
contact polygon, and so does uniqueness; the disk is not used after Step 1.

*Lean: [`Five.attainment`](../../SquaresInCircles/Five/Construction.lean#L40),
[`Five.optimality`](../../SquaresInCircles/Five/Optimality.lean#L36),
[`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L56), in
[`SquaresInCircles/Five/`](../../SquaresInCircles/Five).*

## Construction

### Proposition 5.1 (attainment)

$Q(c_1), \dots, Q(c_5)$ are pairwise disjoint and lie in the closed disk of
radius $R_5$ about the origin.

*Proof.* Any two of the centres differ by at least 1 in one coordinate. Each
square lies in $[-\frac32, \frac32] \times [-\frac12, \frac12]$ or in
$[-\frac12, \frac12] \times [-\frac32, \frac32]$, and
$\frac94 + \frac14 = \frac52$. Apply
[Lemma 20](common.md#lemma-20-axis-parallel-squares). $\square$

*Lean:
[`Five.model_disjoint`](../../SquaresInCircles/Five/Construction.lean#L25),
[`Five.model_packing`](../../SquaresInCircles/Five/Construction.lean#L30),
[`Five.attainment`](../../SquaresInCircles/Five/Construction.lean#L40).*

## Lower bound

### Proposition 5.2 (lower bound)

If five pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R^2 \ge \frac52$.

The proof takes four steps.

1. **The contact polygon.** A smaller disk puts $(a_S, b_S)$ strictly inside
   a 12-gon $P_5$ for every square $S$.
2. **Exterior squares.** Each square that avoids $o$ holds more than a fifth
   of $\Gamma_{5/6}$.
3. **The containing square.** Unless it is centred at $o$, its radial sweep
   holds a fifth of $\Gamma_{5/6}$.
4. **Conclusion.** So some square is centred at $o$, which the strict
   polygon rules out.

*Lean: [`five_squared_lower`](../../SquaresInCircles/Five/Optimality.lean#L30),
[`Five.optimality`](../../SquaresInCircles/Five/Optimality.lean#L36).*

### Step 1. The contact polygon

#### Definition 5.3 (the 12-gon)

$P_5$ is the set of points $(a, b)$ with

```math
3a + b \le 3, \qquad a + 3b \le 3, \qquad a + b \le \sqrt5 - 1 .
```

The first two inequalities are the octagon $P_8$: the tangents to
$\varphi = \frac52$ at $(1, 0)$ and $(0, 1)$. The outer squares of the plus
have $(a_S, b_S) = (1, 0)$. The third is the tangent at
$(\frac{\sqrt5 - 1}2, \frac{\sqrt5 - 1}2)$, also on $\varphi = \frac52$. No
square of the plus touches it; Step 2 needs it.

![The part with a, b at least 0 of the 12-gon P5, around the disk where phi is at most 5/2, touching it at (1, 0), (0, 1) and (g, g)](figures/twelve-gon.svg)

*The 12-gon $P_5$ where $a, b \ge 0$, with $g = \frac{\sqrt5 - 1}2$. Its third
side cuts the corner off the octagon.*

*Lean: [`P5`](../../SquaresInCircles/Five/Tangents.lean#L12),
[`P5Strict`](../../SquaresInCircles/Five/Tangents.lean#L13).*

#### Lemma 5.4 (contact polygon)

If $\varphi(a, b) < \frac52$, then $(a, b)$ is strictly inside $P_5$. If
$\varphi(a, b) \le \frac52$, then $(a, b) \in P_5$.

*Proof.* [Lemma 2](common.md#lemma-2-tangent-lines) at the three points.
$\square$

From here on only the polygon and disjointness are used, and Steps 2 and 3
need only the closed $P_5$.

*Lean: [`p5_contact`](../../SquaresInCircles/Five/Tangents.lean#L15),
[`p5_of_phi_lt`](../../SquaresInCircles/Five/Tangents.lean#L29),
[`p5_of_phi_le`](../../SquaresInCircles/Five/Tangents.lean#L19).*

### Step 2. Exterior squares

#### Lemma 5.5 (an arcsine sum)

If $0 \le x \le \frac12$, $-\frac12 \le y \le \frac12$,
$x + y \le \frac{237}{1000}$ and $3x + y \le 1$, then

```math
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 < \tfrac\pi{10} .
```

*Proof.* If $y \ge 0$, apply the cubic bound of
[Lemma 19](common.md#lemma-19-elementary-estimates) (3) to both terms. With
$s = x + y$ and $x^3 + y^3 \le s^3$,

```math
\arcsin\tfrac{6x}5 + \arcsin\tfrac{6y}5 \le \tfrac65 s + \tfrac{54}{125}s^3 < \tfrac{313}{1000} < \tfrac\pi{10} .
```

If $y < 0$, use $\arcsin\frac{6y}5 \le \frac{6y}5$ for the second term, and
bound $x^3$ directly when $x \le \frac{23}{60}$, or through $3x + y \le 1$
when $x > \frac{23}{60}$. $\square$

*Lean: [`five_arcsin_sum`](../../SquaresInCircles/Five/Exterior.lean#L19).*

#### Lemma 5.6 (exterior arcs)

Let $S$ be exterior with $(a_S, b_S) \in P_5$. Then $S$ holds an arc of
$\Gamma_{5/6}$ of half-width more than $\frac\pi5$.

*Idea.* On this larger circle the arc can reach past the far side of the cap,
so we use the rectangle interval of
[Lemma 14](common.md#lemma-14-the-rectangle-interval), whose figure is drawn on
this circle. Its two ends are arcsines, and the 12-gon keeps them far enough
apart.

*Proof.* Here $b_S \le a_S$, $a_S \ge \frac12$, and $a_S \le 1$ by the
octagon. Put $x = a_S - \frac12 \in [0, \frac12]$ and
$y = b_S - \frac12 \in [-\frac12, \frac12]$. The near corner $(x, y)$ satisfies
$x^2 + y^2 \le \frac12 < \frac{25}{36}$, so it lies inside $\Gamma_{5/6}$, and
$\frac56 < a_S + \frac12$. By Lemma 14 it suffices to show that both

```math
\arccos\tfrac{6x}5 - \arcsin\tfrac{6y}5 \qquad \text{and} \qquad \arcsin\tfrac{6(b_S + 1/2)}5 - \arcsin\tfrac{6y}5
```

exceed $\frac{2\pi}5$.

- *The first.* Since $\arccos\frac{6x}5 = \frac\pi2 - \arcsin\frac{6x}5$, it
  exceeds $\frac{2\pi}5$ exactly when
  $\arcsin\frac{6x}5 + \arcsin\frac{6y}5 < \frac\pi{10}$. The polygon gives
  $x + y \le \sqrt5 - 2 < \frac{237}{1000}$ and $3x + y \le 1$, so Lemma 5.5
  applies.
- *The second.* If $b_S + \frac12 \ge \frac56$ its first arcsine is
  $\frac\pi2 \ge \arccos\frac{6x}5$, and the first bound applies. Otherwise
  it equals $\arcsin\frac{6(b_S + 1/2)}5 + \arcsin\frac{6(1/2 - b_S)}5$, whose two
  arguments average $\frac35 > \sin\frac\pi5$; Lemma 19 (4) gives more than
  $\frac{2\pi}5$. $\square$

*Lean: [`sqrt_five_lt_2237`](../../SquaresInCircles/Five/Exterior.lean#L14),
[`five_rectangle_length`](../../SquaresInCircles/Five/Exterior.lean#L44),
[`five_exterior_arc`](../../SquaresInCircles/Five/Exterior.lean#L87).*

### Step 3. The containing square

#### Lemma 5.7 (the sweep holds a fifth of the circle)

Let $S$ contain $o$, with $c_S \ne o$. Then $\widehat{S}$ holds an arc of
$\Gamma_{5/6}$ of half-width $\frac\pi5$.

*Idea.* Slide $S$ outward until its centre is at distance $\frac1{\sqrt2}$
from $o$. Its inscribed disk then covers a fifth of $\Gamma_{5/6}$, even when
$S$ itself does not reach the circle (see the figure in
[Definition 17](common.md#definition-17-radial-sweep)).

![A square containing o, slid outward along the ray from o through its centre until its centre c* is at distance 1 over root 2 from o; the inscribed disk of the slid square covers a highlighted fifth of the circle of radius 5/6](figures/slid-disk.svg)

*The slid copy of $S$, centred at $c^*$, and its inscribed disk. The disk covers
the arc of $\Gamma_{5/6}$ of half-width $\frac\pi5$ about the direction of
$c_S - o$.*

*Proof.* Since $a_S, b_S < \frac12$,
[Lemma 1](common.md#lemma-1-farthest-vertex) gives
$|c_S - o|^2 = a_S^2 + b_S^2 < \frac12$. Let $\theta$ be the direction of
$c_S - o$, and slide $S$ away from $o$ until its centre reaches
$c^* = o + \frac1{\sqrt2}u(\theta)$. The open disk of radius $\frac12$ about
$c^*$ lies in the slid square
([Lemma 3](common.md#lemma-3-inscribed-disks) (1)), hence in $\widehat{S}$.
For $|t| < \frac\pi5$, the point $p = o + \frac56 u(\theta + t)$ satisfies, by
the law of cosines and Lemma 19 (5),

```math
|p - c^*|^2 = \tfrac{25}{36} + \tfrac12 - 2\cdot\tfrac56\cdot\tfrac1{\sqrt2}\cos t
< \tfrac{25}{36} + \tfrac12 - \tfrac53\cdot\tfrac{707}{1000}\cdot\tfrac{401}{500} < \tfrac14 ,
```

using $\frac1{\sqrt2} > \frac{707}{1000}$. So $p \in \widehat{S}$. $\square$

A square centred at $o$ gets no arc from this lemma; Step 4 deals with it.

*Lean:
[`containing_center_norm`](../../SquaresInCircles/Five/Containing.lean#L9),
[`containing_ray_disk`](../../SquaresInCircles/Five/Containing.lean#L41),
[`five_arc_in_radial_disk`](../../SquaresInCircles/Five/Containing.lean#L69),
[`five_containing_arc`](../../SquaresInCircles/Five/Containing.lean#L84).*

### Step 4. Conclusion

#### Proposition 5.8 (a centred square)

If five pairwise disjoint squares $S$ all have $(a_S, b_S) \in P_5$, one of
them is centred at $o$.

*Proof.* Suppose none is. Every $(a_S, b_S)$ lies in the octagon $P_8$.

- A containing square is not centred at $o$, so its sweep holds an arc of
  half-width $\frac\pi5$ (Lemma 5.7).
- Every exterior square holds more than that (Lemma 5.6).

This contradicts [Proposition 18](common.md#proposition-18-budget-with-a-sweep)
with $n = 5$ and $r = \frac56$. $\square$

*Lean:
[`five_centered_square`](../../SquaresInCircles/Five/Optimality.lean#L12).*

#### Corollary 5.9 (polygon relaxation)

No five pairwise disjoint squares $S$ all have $(a_S, b_S)$ strictly inside
$P_5$.

*Proof.* By Proposition 5.8 some square is centred at $o$. The other squares
are strictly inside the octagon, and
[Lemma 17](common.md#lemma-17-no-centred-square) rules the centred square
out. $\square$

*Lean:
[`five_polygon_strict_impossible`](../../SquaresInCircles/Five/Optimality.lean#L23).*

*Proof of Proposition 5.2.* If $R^2 < \frac52$, then by Lemma 1 and
Lemma 5.4, $(a_S, b_S)$ is strictly inside $P_5$ for every square $S$, which
Corollary 5.9 excludes.
$\square$

## Uniqueness

*Idea.* Proposition 5.8 needs only the closed 12-gon, so at radius $R_5$ it
still gives a square centred at $o$. The 12-gon also keeps every centre
within 1 of $o$, while disjointness keeps the others at least 1 from the
centred square. So they are side-neighbours of it.

### Lemma 5.10 (the 12-gon lies in the unit disk)

If $a, b \ge 0$ and $(a, b) \in P_5$, then $a^2 + b^2 \le 1$.

![The part with a, b at least 0 of the 12-gon P5, inside the quarter of the unit circle, touching it at (1, 0) and (0, 1)](figures/dodecagon-disk.svg)

*The 12-gon stays inside the unit circle $a^2 + b^2 = 1$ and touches it only at
$(1, 0)$ and $(0, 1)$.*

*Proof.* If $a + b \le 1$, then $a^2 + b^2 \le (a + b)^2 \le 1$. Otherwise
$s = a + b$ lies in $(1, \frac75)$, since $\sqrt5 - 1 < \frac75$, and the
octagon gives $|a - b| \le 3 - 2s$. Then

```math
2\left(a^2 + b^2\right) = s^2 + (a - b)^2 \le s^2 + (3 - 2s)^2 = 2 + (5s - 7)(s - 1) < 2 . \qquad \square
```

*Lean: [`dodecagon_norm_le`](../../SquaresInCircles/Five/Uniqueness.lean#L10).*

### Proposition 5.11 (the 12-gon is rigid)

If five pairwise disjoint squares $S$ all have $(a_S, b_S) \in P_5$, they
have the normal form of $c_1, \dots, c_5$.

The statement mentions no disk, which makes it stronger than uniqueness for
the packing problem.

*Proof.*

1. **A centred square.** By Proposition 5.8 some square $S_0$ has
   $c_{S_0} = o$.
2. **Unit contacts.** By Lemma 5.10 and Lemma 1, every centre is within 1 of
   $o$. By [Lemma 4](common.md#lemma-4-centres-at-least-1-apart) every other
   centre is at least 1 from $c_{S_0} = o$, so exactly 1. By
   [Lemma 6](common.md#lemma-6-squares-at-distance-1), each of the other four
   squares has sides parallel to those of $S_0$ and shares a full edge with
   it.
3. **The plus.** In the frame of $S_0$, the square $S_0$ sits at $(0, 0)$ and
   the other four at $(\pm1, 0)$ and $(0, \pm1)$
   ([Lemma 21](common.md#lemma-21-sitting-at-a-centre) (1)).
   [Lemma 22](common.md#lemma-22-from-slots-to-a-normal-form) gives the normal
   form. No angle has to be computed. $\square$

*Lean:
[`Five.polygon_uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L27).*

### Corollary 5.12 (uniqueness)

If five pairwise disjoint unit squares lie in the closed disk of radius $R_5$
about $o$, the packing has the normal form of $c_1, \dots, c_5$.

*Proof.* By Lemma 1 and Lemma 5.4, $(a_S, b_S) \in P_5$ for every square $S$;
apply Proposition 5.11. $\square$

*Lean: [`Five.uniqueness`](../../SquaresInCircles/Five/Uniqueness.lean#L56).*