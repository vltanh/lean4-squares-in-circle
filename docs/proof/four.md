# Four squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 4.** Let $R_4 = \sqrt2$, and let $c_1, \dots, c_4$ be the points
$(\frac12, \frac12)$, $(-\frac12, \frac12)$, $(-\frac12, -\frac12)$,
$(\frac12, -\frac12)$.

1. $Q(c_1), \dots, Q(c_4)$ form a packing in the closed disk of radius $R_4$
   about the origin: the $2 \times 2$ block.
2. A packing of four unit squares in a closed disk of radius $R$ forces
   $R \ge R_4$.
3. A packing of four unit squares in a closed disk of radius $R_4$ has the
   normal form of $c_1, \dots, c_4$. In particular the disk centre is a
   vertex of every square.

![The 2 by 2 block in its dashed circle of radius root 2, with the circle of radius 1/2 about the centre divided into four coloured quarter arcs, one in each square](figures/four.svg)

*The block. The circle $\Gamma_{1/2}$ about the disk centre $o$
splits into four quarter circles, one in each square.*

*Sketch.* Draw the circle $\Gamma_{1/2}$ about the disk centre. In a smaller
disk, every square that avoids the centre holds more than a quarter of it. A
square that contains the centre may hold less, but its radial sweep holds a
full quarter and still avoids the other squares. Four arcs of a quarter or
more, one of them longer, do not fit. At radius exactly $\sqrt2$ every arc is
exactly a quarter, which puts a vertex of each square at the centre.

Unlike three and five squares, this case keeps the disk constraint
$\varphi(a_S, b_S) \le 2$ next to the contact polygon throughout: the exterior
arcs need it, and so does uniqueness, because the polygon alone is not rigid.

*Lean: [`Four.attainment`](../../SquaresInCircles/Four/Construction.lean#L35),
[`Four.optimality`](../../SquaresInCircles/Four/Optimality.lean#L38),
[`Four.uniqueness`](../../SquaresInCircles/Four/Uniqueness.lean#L120), in
[`SquaresInCircles/Four/`](../../SquaresInCircles/Four).*

## Construction

### Proposition 4.1 (attainment)

$Q(c_1), \dots, Q(c_4)$ are pairwise disjoint and lie in the closed disk of
radius $\sqrt2$ about the origin.

*Proof.* Any two of the centres differ by 1 in one coordinate, and all four
squares lie in $[-1, 1]^2$, with $1 + 1 = 2$. Apply
[Lemma 20](common.md#lemma-20-axis-parallel-squares). $\square$

*Lean:
[`Four.model_disjoint`](../../SquaresInCircles/Four/Construction.lean#L24),
[`Four.model_packing`](../../SquaresInCircles/Four/Construction.lean#L29),
[`Four.attainment`](../../SquaresInCircles/Four/Construction.lean#L35).*

## Lower bound

### Proposition 4.2 (lower bound)

If four pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R^2 \ge 2$.

The proof takes four steps.

1. **The contact polygon.** A smaller disk puts $(a_S, b_S)$ strictly inside
   the diamond $a + b < 1$ for every square $S$.
2. **Exterior squares.** Each square that avoids $o$ holds more than a quarter
   of $\Gamma_{1/2}$.
3. **The containing square.** Its radial sweep holds a full quarter of
   $\Gamma_{1/2}$.
4. **Conclusion.** The angular budget fails.

*Lean: [`four_squared_lower`](../../SquaresInCircles/Four/Optimality.lean#L31),
[`Four.optimality`](../../SquaresInCircles/Four/Optimality.lean#L38).*

### Step 1. The contact polygon

#### Lemma 4.3 (the diamond)

1. If $\varphi(a, b) \le 2$, then $a + b \le 1$.
2. If $\varphi(a, b) < 2$, then $a + b < 1$; for $a, b \ge 0$ this puts
   $(a, b)$ strictly inside the octagon $P_8$.

![The (a, b)-plane: the disk where phi is at most 2, inside the triangle a plus b at most 1, which touches it at (1/2, 1/2); dashed, the larger octagon](figures/diamond.svg)

*The diamond $a + b \le 1$, where $a, b \ge 0$, is the tangent half-plane at
$(\frac12, \frac12)$. It lies inside the octagon $P_8$.*

*Proof.* In the block every square has $(a_S, b_S) = (\frac12, \frac12)$,
which lies on $\varphi = 2$, and the tangent half-plane there is $a + b \le 1$
([Lemma 2](common.md#lemma-2-tangent-lines)). For the octagon,
$3a + b \le 3(a + b) < 3$, and likewise $a + 3b < 3$. $\square$

We call $a + b \le 1$ the *diamond*.

*Lean: [`P4`](../../SquaresInCircles/Four/Tangents.lean#L12),
[`P4Strict`](../../SquaresInCircles/Four/Tangents.lean#L13),
[`p4_of_phi_le`](../../SquaresInCircles/Four/Tangents.lean#L15),
[`p4_of_phi_lt`](../../SquaresInCircles/Four/Tangents.lean#L19),
[`p4Strict_to_p8Strict`](../../SquaresInCircles/Four/Tangents.lean#L23).*

### Step 2. Exterior squares

#### Lemma 4.4 (exterior caps)

Let $S$ be exterior with $\varphi(a_S, b_S) \le 2$. Then $S$ holds a cap of
$\Gamma_{1/2}$ of length at least $\frac\pi2$, and more than $\frac\pi2$
unless $a_S + b_S = 1$.

*Proof.* On $\Gamma_{1/2}$ the cap angles of $S$ are

```math
A_S = \arccos(2a_S - 1), \qquad V_S = \arcsin(1 - 2b_S) .
```

If $a_S \ge \frac56$ then $\varphi(a_S, b_S) \ge (\frac43)^2 + \frac14 > 2$, so
$a_S < \frac56$ and $a_S - \frac12 < \frac12$. With
$b_S \le 1 - a_S \le \frac12$ (Lemma 4.3), [Lemma 13](common.md#lemma-13-the-cap)
applies: the cap has length $\min(2A_S, A_S + V_S)$.

- $2a_S - 1 < \frac23 < \frac{\sqrt2}2 = \cos\frac\pi4$, so $A_S > \frac\pi4$
  and $2A_S > \frac\pi2$.
- $a_S + b_S \le 1$ gives $2a_S - 1 \le 1 - 2b_S$, so
  $\frac\pi2 - A_S = \arcsin(2a_S - 1) \le V_S$, that is
  $A_S + V_S \ge \frac\pi2$, and strictly if $a_S + b_S < 1$. $\square$

This is where the disk matters: the diamond alone allows $a_S$ up to 1, and at
$a_S = 1$ the cap shrinks to nothing.

*Lean: [`four_exterior_arc`](../../SquaresInCircles/Four/Exterior.lean#L13).*

### Step 3. The containing square

#### Lemma 4.5 (a test for the sweep)

Let $a_S > 0$, and let $(X, Y)$ be a point in the chart of $S$. If

```math
X > a_S - \tfrac12, \qquad Y > b_S - \tfrac12, \qquad |b_S X - a_S Y| < \tfrac{a_S + b_S}2 ,
```

then the point lies in the radial sweep $\widehat{S}$.

The first two conditions put the point ahead of the back edges of $S$; the
third puts it inside the band that $S$ sweeps out.

![A containing square in its chart, the band it sweeps out along the ray from o through its centre, the dashed lines of its two back edges, and a highlighted quarter of a circle about o lying in the sweep](figures/sweep-test.svg)

*The sweep $\widehat{S}$ is the band between the dashed lines, ahead of the back
edges $X = a_S - \frac12$ and $Y = b_S - \frac12$. The highlighted quarter
circle is the arc of Lemma 4.6.*

*Proof.* By the chart condition, we need $s = 1 + m \ge 1$ with
$|X - s a_S| < \frac12$ and $|Y - s b_S| < \frac12$.

- The first asks for $s$ in $(\frac{X - 1/2}{a_S}, \frac{X + 1/2}{a_S})$, an
  interval that reaches beyond 1 because $X > a_S - \frac12$.
- If $b_S = 0$, the band condition reads $|Y| < \frac12$, and any such $s$
  works.
- If $b_S > 0$, the second asks for $s$ in
  $(\frac{Y - 1/2}{b_S}, \frac{Y + 1/2}{b_S})$, which also reaches beyond 1,
  and the band condition says exactly that the two intervals overlap.
  $\square$

*Lean: [`ray_parameter`](../../SquaresInCircles/Four/Containing.lean#L16),
[`SquareChart.ray_mem`](../../SquaresInCircles/Common/Charts.lean#L84).*

#### Lemma 4.6 (the sweep holds a quarter circle)

Let $S$ contain $o$, with $c_S \ne o$. Then $\widehat{S}$ holds an arc of
half-width $\frac\pi4$, centred at the direction of $c_S - o$, on every circle
$\Gamma_r$ with $0 < r < \frac1{\sqrt2}$
([Definition 17](common.md#definition-17-radial-sweep)).

The arc is highlighted in the figure of
[Lemma 4.5](#lemma-45-a-test-for-the-sweep).

*Proof.* Here $0 \le b_S \le a_S < \frac12$, and $a_S > 0$ because
$c_S \ne o$. Write $(a_S, b_S) = \ell(\cos\delta, \sin\delta)$, with
$0 \le \delta \le \frac\pi4$ and $a_S \le \ell \le a_S + b_S$. For
$|t - \delta| < \frac\pi4$ we check Lemma 4.5 at $X = r\cos t$,
$Y = r\sin t$.

- $t \in (-\frac\pi4, \frac\pi2)$, so $X > 0 > a_S - \frac12$.
- $b_S X - a_S Y = -r\ell\sin(t - \delta)$ with
  $|\sin(t - \delta)| < \frac1{\sqrt2}$ and $r < \frac1{\sqrt2}$, so
  $|b_S X - a_S Y| < \frac\ell2 \le \frac{a_S + b_S}2$.
- $\sin t > \sin(\delta - \frac\pi4) = \frac{b_S - a_S}{\sqrt2 \ell}$. As
  $b_S - a_S \le 0$ and $\frac r{\sqrt2} < \frac12$, this gives
  $Y > \frac{b_S - a_S}{2\ell}$, and $\frac{b_S - a_S}{2\ell} \ge b_S - \frac12$
  because $\ell(1 - 2b_S) \ge a_S(1 - 2b_S) \ge a_S - b_S$ (the last since
  $a_S < \frac12$).

These chart angles form an arc of half-width $\frac\pi4$ centred at
$\theta_S + \varepsilon_S\delta$, the direction of $c_S - o$. $\square$

*Lean:
[`first_octant_direction`](../../SquaresInCircles/Four/Containing.lean#L59),
[`canonical_quarter_ray`](../../SquaresInCircles/Four/Containing.lean#L94),
[`four_containing_arc`](../../SquaresInCircles/Four/Containing.lean#L154).*

### Step 4. Conclusion

#### Proposition 4.7 (diamond relaxation)

No four pairwise disjoint squares $S$ all satisfy $\varphi(a_S, b_S) \le 2$
and $a_S + b_S < 1$.

*Proof.* By Lemma 4.3 every $(a_S, b_S)$ is strictly inside the octagon.

- If a square contains $o$: some other square is strictly inside the octagon,
  so the containing square is not centred at $o$
  ([Lemma 17](common.md#lemma-17-no-centred-square)), and by Lemma 4.6 its
  sweep holds a quarter circle of $\Gamma_{1/2}$.
- Every exterior square holds more than a quarter circle (Lemma 4.4, since
  $a_S + b_S < 1$).

This contradicts [Proposition 18](common.md#proposition-18-budget-with-a-sweep)
with $n = 4$ and $r = \frac12$. $\square$

*Lean:
[`four_diamond_impossible`](../../SquaresInCircles/Four/Optimality.lean#L13).*

*Proof of Proposition 4.2.* If $R^2 < 2$, then by
[Lemma 1](common.md#lemma-1-farthest-vertex) every square $S$ has
$\varphi(a_S, b_S) < 2$, hence $a_S + b_S < 1$ (Lemma 4.3), which
Proposition 4.7 excludes. $\square$

## Uniqueness

*Idea.* At radius exactly $\sqrt2$, the identity

```math
\varphi(a, b) - 2 = 2(a + b - 1) + \left(a - \tfrac12\right)^2 + \left(b - \tfrac12\right)^2
```

shows that a square with $a_S + b_S = 1$ must have $a_S = b_S = \frac12$, that
is, a vertex at $o$. Proposition 4.7 produces one such square; then no square
contains $o$, the arcs are exactly quarters, and every square has a vertex at
$o$.

### Lemma 4.8 (a closed square keeps out of other squares)

If $S$ and $T$ are disjoint and $p \in \overline{S}$, then $p \notin T^\circ$.

*Proof.* With $n$ from [Lemma 5](common.md#lemma-5-supporting-line), every
$q \in T^\circ$ satisfies

```math
\langle n, p\rangle \le \langle n, c_S\rangle + w_S(n) \le \langle n, c_T\rangle - w_T(n) < \langle n, q\rangle . \qquad \square
```

*Lean: [`closed_dot_bound`](../../SquaresInCircles/Four/Uniqueness.lean#L10),
[`closed_open_disjoint`](../../SquaresInCircles/Four/Uniqueness.lean#L21).*

### Lemma 4.9 (a square with a vertex at the disk centre)

Let $a_S = b_S = \frac12$, and let $\mu_S = \theta_S + \varepsilon_S\frac\pi4$.
Then

1. $S$ holds the arc of $\Gamma_{1/2}$ of half-width $\frac\pi4$ centred at
   $\mu_S$;
2. $S$ sits at $(\frac12, \frac12)$ in the frame $\mu_S - \frac\pi4$.

![A tilted square with a vertex at o, the quarter of the circle of radius 1/2 between its two edges from o highlighted, and the bisecting direction mu_S dashed](figures/vertex-square.svg)

*The two edges of $S$ from $o$ point in the directions $\mu_S \pm \frac\pi4$,
and $S$ holds the quarter of $\Gamma_{1/2}$ between them.*

*Proof.* In its chart, $S$ is the open square $(0, 1)^2$, with a vertex at
$o$.

1. For $0 < t < \frac\pi2$ the point $(\frac12\cos t, \frac12\sin t)$ lies in
   $(0, 1)^2$; apply [Lemma 10](common.md#lemma-10-charts) (2).
2. $S$ spans the directions from $\mu_S - \frac\pi4$ to $\mu_S + \frac\pi4$.
   If $\varepsilon_S = 1$ this is
   [Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart). If
   $\varepsilon_S = -1$, Lemma 11 places $S$ at $(\frac12, -\frac12)$ in the
   frame $\theta_S$, and a quarter turn
   ([Lemma 21](common.md#lemma-21-sitting-at-a-centre) (2)) moves it to
   $(\frac12, \frac12)$ in the frame $\mu_S - \frac\pi4$. $\square$

*Lean: [`vertexMid`](../../SquaresInCircles/Four/Uniqueness.lean#L80),
[`vertex_arc`](../../SquaresInCircles/Four/Uniqueness.lean#L83),
[`vertex_represents`](../../SquaresInCircles/Four/Uniqueness.lean#L97).*

### Proposition 4.10 (uniqueness)

If four pairwise disjoint unit squares lie in the closed disk of radius
$\sqrt2$ about $o$, the packing has the normal form of $c_1, \dots, c_4$.

*Proof.* Every square $S$ has $\varphi(a_S, b_S) \le 2$, hence
$a_S + b_S \le 1$. By the identity above, $a_S + b_S \ge 1$ forces
$a_S = b_S = \frac12$.

1. **Some square has a vertex at $o$.** Otherwise every square would have
   $a_S + b_S < 1$, which Proposition 4.7 excludes.
2. **No square contains $o$.** The point $o$ lies in the closed square of the
   square $S$ found in (1). So it lies in no other open square (Lemma 4.8),
   and not in $S^\circ$ either, since $a_S = \frac12$.
3. **Every square has a vertex at $o$.** All four squares are exterior, so
   each $S$ holds a cap of length at least $\frac\pi2$, and more unless
   $a_S + b_S = 1$ (Lemma 4.4). The angular budget
   ([Lemma 7](common.md#lemma-7-angular-budget)) forces $a_S + b_S = 1$,
   hence $a_S = b_S = \frac12$, for all four.
4. **The block.** By Lemma 4.9 the squares hold disjoint quarter arcs of
   $\Gamma_{1/2}$, centred at their directions $\mu_S$. These are pairwise at
   least $\frac\pi2$ apart
   ([Lemma 8](common.md#lemma-8-disjoint-arcs-have-separated-centres)), so
   they are $\mu_0 + k\frac\pi2$ for some $\mu_0$
   ([Lemma 23](common.md#lemma-23-four-directions)). In the frame
   $\mu_0 - \frac\pi4$ each square sits at $(\frac12, \frac12)$ turned by its
   $k$ quarter turns (Lemmas 4.9 and 21), which is one of
   $c_1, \dots, c_4$. [Lemma 22](common.md#lemma-22-from-slots-to-a-normal-form)
   gives the normal form. $\square$

*Lean: [`four_contact_eq`](../../SquaresInCircles/Four/Uniqueness.lean#L32),
[`four_some_vertex`](../../SquaresInCircles/Four/Uniqueness.lean#L39),
[`four_no_containing`](../../SquaresInCircles/Four/Uniqueness.lean#L50),
[`four_all_vertices`](../../SquaresInCircles/Four/Uniqueness.lean#L65),
[`Four.uniqueness`](../../SquaresInCircles/Four/Uniqueness.lean#L120).*