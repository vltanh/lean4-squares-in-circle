# The proof

[Back to the README](../../README.md)

These pages give the Lean proofs as ordinary mathematics. The setting comes
first, in [preliminaries.md](preliminaries.md). The tools that several cases
share are defined and proved once in [common.md](common.md), and each case has
its own page. Every result is stated before it is proved, and ends with a link
to the Lean declarations it follows.

**How to read them.** Start with the plan below, then open a case page. Each
case page begins with a picture of the optimal packing and a sketch of the
whole argument, and each longer proof begins with its idea in a few
sentences. Look up a shared lemma or a definition only when a proof cites it;
the [notation table](preliminaries.md#notation-at-a-glance) lists every
symbol. The figures are drawn from the same geometry by
[`scripts/proof_figures.py`](../../scripts/proof_figures.py).

| page | contents |
| --- | --- |
| [preliminaries.md](preliminaries.md) | the setting: notation, conventions, and Definitions 1 to 5 (squares, packings, normal forms) |
| [common.md](common.md) | the shared toolkit: Definitions 6 to 17 and Lemmas 1 to 23, each tool defined where it is first used |
| [one.md](one.md) | Theorem 1, one square |
| [two.md](two.md) | Theorem 2, two squares |
| [three.md](three.md) | Theorem 3, three squares |
| [four.md](four.md) | Theorem 4, four squares |
| [five.md](five.md) | Theorem 5, five squares |
| [seven.md](seven.md) | Theorem 7, seven squares |

## The main theorem

*Lean: [`optimality`](../../SquaresInCircles.lean#L43),
[`attainment`](../../SquaresInCircles.lean#L55),
[`uniqueness`](../../SquaresInCircles.lean#L66),
[`sliding_uniqueness`](../../SquaresInCircles.lean#L79) in
[`SquaresInCircles.lean`](../../SquaresInCircles.lean).*

For $1 \le n \le 5$ and $n = 7$ let $R_n$ and $c_1, \dots, c_n$ be given by the
table.

| $n$ | $R_n$ | $c_1, \dots, c_n$ | packing |
| :-: | :-: | --- | --- |
| 1 | $\frac{\sqrt2}2$ | $(0, 0)$ | the square |
| 2 | $\frac{\sqrt5}2$ | $(-\frac12, 0)$, $(\frac12, 0)$ | the $2 \times 1$ rectangle |
| 3 | $\frac{5\sqrt{17}}{16}$ | $(-\frac12, -\frac5{16})$, $(\frac12, -\frac5{16})$, $(0, \frac{11}{16})$ | the T |
| 4 | $\sqrt2$ | $(\frac12, \frac12)$, $(-\frac12, \frac12)$, $(-\frac12, -\frac12)$, $(\frac12, -\frac12)$ | the $2 \times 2$ block |
| 5 | $\sqrt{5/2}$ | $(0, 0)$, $(1, 0)$, $(0, 1)$, $(-1, 0)$, $(0, -1)$ | the plus |
| 7 | $\frac{\sqrt{13}}2$ | $(1, -\frac12)$, $(1, \frac12)$, $(-1, -\frac12)$, $(-1, \frac12)$, $(0, -1)$, $(0, 0)$, $(0, 1)$ | two columns of two beside a column of three |

**Theorem.** Let $1 \le n \le 5$ or $n = 7$.

1. *Attainment.* The axis-parallel squares $Q(c_1), \dots, Q(c_n)$ form a
   packing in the closed disk of radius $R_n$ about the origin
   (Definitions 2 and 3).
2. *Optimality.* If $n$ unit squares form a packing in a closed disk of
   radius $R$, then $R \ge R_n$.
3. *Uniqueness.* For $n \le 5$, every packing of $n$ unit squares in a closed
   disk of radius $R_n$ has the normal form of $c_1, \dots, c_n$
   (Definition 5): one rotation about the disk centre and one relabelling
   carry the model onto it. For $n = 7$ the same holds with $c_5, c_6, c_7$
   replaced by $(0, y_1), (0, y_2), (0, y_3)$ for some heights that are at
   least 1 apart and within $\sqrt3 - \frac12$ of 0: the middle column can
   slide.

The case $n$ is Theorem $n$ on the page for that case.

## One and two squares

The farthest-vertex bound of
[Lemma 1](common.md#lemma-1-farthest-vertex) settles one square at once, since
$\varphi(a_S, b_S) \ge \frac12$. For two squares it puts both centres within
$\frac12$ of the disk centre in any smaller disk, while centres of disjoint
squares are at least 1 apart; the parallelogram law shows the two facts are
incompatible.

## Three to five squares

The lower bound is a proof by contradiction. Assume a packing in a disk with
$R^2$ below $R_n^2$.

1. **The contact polygon.** Lemma 1 gives $\varphi(a_S, b_S) < R^2$ for every
   square, and the tangent half-planes of
   [Lemma 2](common.md#lemma-2-tangent-lines) at the contact points of the
   optimal packing turn this curved constraint into a polygon. From here on
   the disk is forgotten, except for four squares.
2. **Exterior squares.** On a small auxiliary circle about the disk centre,
   every square that does not contain the centre holds an arc longer than
   $\frac{2\pi}n$.
3. **The containing square.** At most one square contains the disk centre.
   Its own arc can be short, and each case handles it separately.
4. **Conclusion.** The arcs of disjoint squares cannot take up more than the
   whole circle ([Lemma 7](common.md#lemma-7-angular-budget)), so
   $R^2 \ge R_n^2$.

For uniqueness the same argument runs at the optimal radius with equality
allowed. Every inequality in the chain must then be tight, and the tight
configurations are rebuilt exactly.

### Where the cases differ

| | three | four | five |
| --- | --- | --- | --- |
| target $R^2$ | $\frac{425}{256}$ | $2$ | $\frac52$ |
| **1.** tangent points | $(\frac12, \frac5{16})$, $(\frac{11}{16}, 0)$ and mirrors | $(\frac12, \frac12)$ | $(1, 0)$, $(0, 1)$, $(\frac{\sqrt5-1}2, \frac{\sqrt5-1}2)$ |
| **1.** polygon | the 16-gon $P_3$ | the diamond $a + b < 1$ | the 12-gon $P_5$ |
| **1.** disk used afterwards | no | yes, $\varphi \le 2$ | no |
| **2.** auxiliary radius | $\frac38$ | $\frac12$ | $\frac56$ |
| **2.** exterior arc | a cap longer than 120° | a cap longer than 90° | an interval longer than 72° |
| **3.** containing square | its own arc; no clipped cap; an explicit common point | radial sweep, 90° | radial sweep, 72°, unless centred at the disk centre |
| **4.** budget | three arcs (Lemma 9) | sweep (Proposition 18) | sweep (Proposition 18) |
| uniqueness: tight case | no square contains the centre; three caps of exactly 120° | the centre is a vertex of every square | a centred square; the others at distance 1 |
| uniqueness: assumes | $\varphi \le \frac{425}{256}$ | $\varphi \le 2$ | the closed 12-gon only |
| uniqueness: rebuilt from | angles between arc centres | a quarter grid of arc centres | unit contacts |

## Seven squares

The lower bound is again a proof by contradiction, but it compares pairs of
squares rather than arcs on one circle. Assume a packing in a disk with
$R^2 < \frac{13}4$.

1. **Six exterior squares.** At most one square contains the disk centre, so
   six squares avoid it.
2. **Markers.** Each exterior square gets a marker, a direction from the disk
   centre computed from the position of the centre relative to the square.
3. **The pair theorem.** Two disjoint exterior squares have markers at least
   $\frac\pi3$ apart, and exactly $\frac\pi3$ apart only if they touch as
   in the optimal packing, which needs $R^2 = \frac{13}4$. The proof puts the
   pair in a normal position, writes the overlaps of their shadows on the four
   edge directions in closed form, and shows that they are positive for every
   gap below $\frac\pi3$ and vanish at $\frac\pi3$ only at those contacts.
4. **Conclusion.** Six directions pairwise at least $\frac\pi3$ apart form a
   regular hexagon ([Lemma 23](common.md#lemma-23-regular-polygons)), so they
   cannot be pairwise more than $\frac\pi3$ apart.

At the optimal radius the six markers are exactly $\frac\pi3$ apart, and the
middle column of the packing can slide without changing them. Uniqueness uses
the same pair theorem: some square contains the centre, the markers of the
other six form a regular hexagon, neighbouring exterior squares touch as in
the optimal packing, and that rebuilds the packing up to the sliding column.

## Shared lemmas by case

The cells list the lemmas of [common.md](common.md) that each part of a proof
depends on, including those used only inside other shared lemmas. Every
construction uses Lemma 20 and nothing else.

**Optimality.**

| section of common.md | 1 | 2 | 3 | 4 | 5 | 7 |
| --- | :-: | :-: | :-: | :-: | :-: | :-: |
| 1. the disk centre seen from a square | 1 | 1 | 1 | 1 | 1 | 1 |
| 2. contact polygons | | | 2 | 2 | 2 | |
| 3. two disjoint squares | | 3, 4 | 3 | 5 | 3, 5 | 5 |
| 4. angular budget | | | 7, 8, 9 | 7 | 7 | |
| 5. charts | | | 10, 11 | 10 | 10 | 10, 11 |
| 6. exterior arcs | | | 12, 13 | 12, 13 | 12, 14 | |
| 7. radial sweep | | | | 15 to 18 | 15 to 18 | |
| 8. elementary estimates | | | 19 | | 19 | 19 |
| 10. normal forms | | | | | | 23 |

**Uniqueness.** Each uniqueness proof reruns part of the optimality argument
at the optimal radius; the table lists only the lemmas it adds.

| | 1 | 2 | 3 | 4 | 5 | 7 |
| --- | :-: | :-: | :-: | :-: | :-: | :-: |
| reuses | Proposition 1.2 | Lemma 2.2 | Proposition 3.11 | Proposition 4.7 | Proposition 5.8 | Theorem 7.16 |
| 3. two disjoint squares | | 5, 6 | | 5 | 4, 6 | 5 |
| 4. angular budget | | | | 8 | | 7 |
| 5. charts | | | | 11 | | |
| 10. normal forms | 21, 22 | 21, 22 | 21, 22 | 21, 23 | 21, 22 | 21, 22 |

## The legacy proof of three squares

The first formalization of three squares was a certificate proof by case
enumeration, kept on the `legacy` branch. It is described at the end of
[three.md](three.md#the-legacy-certificate-proof).
