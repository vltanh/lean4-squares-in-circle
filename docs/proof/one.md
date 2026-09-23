# One square

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 1.** Let $R_1 = \frac{\sqrt2}2$.

1. The square $Q(0, 0)$ lies in the closed disk of radius $R_1$ about the
   origin.
2. A unit square in a closed disk of radius $R$ forces $R \ge R_1$.
3. A unit square in a closed disk of radius $R_1$ is centred at the disk
   centre; the packing has the normal form of $(0, 0)$.

![One unit square centred at the disk centre o, its four vertices on the dashed circle of radius root 2 over 2](figures/one.svg)

*One square. Its vertices lie on the circle of radius $R_1$ about its centre.*

*Sketch.* Some vertex of the square is at least half a diagonal from the disk
centre, with equality only when the square is centred there.

*Lean: [`One.attainment`](../../SquaresInCircles/One/Construction.lean#L33),
[`One.optimality`](../../SquaresInCircles/One/Optimality.lean#L21),
[`One.uniqueness`](../../SquaresInCircles/One/Uniqueness.lean#L9), in
[`SquaresInCircles/One/`](../../SquaresInCircles/One).*

## Construction

### Proposition 1.1 (attainment)

$\overline{Q(0, 0)}$ lies in the closed disk of radius $\frac{\sqrt2}2$ about
the origin.

*Proof.* The square lies in $[-\frac12, \frac12]^2$, and
$\frac14 + \frac14 = \frac12$; apply
[Lemma 20](common.md#lemma-20-axis-parallel-squares). $\square$

*Lean: [`One.model_packing`](../../SquaresInCircles/One/Construction.lean#L25),
[`One.attainment`](../../SquaresInCircles/One/Construction.lean#L33).*

## Lower bound

### Proposition 1.2 (lower bound)

If a unit square lies in the closed disk of radius $R$ about $o$, then
$R^2 \ge \frac12$.

*Proof.* Call the square $S$. By [Lemma 1](common.md#lemma-1-farthest-vertex),
and since $a_S, b_S \ge 0$,

```math
R^2 \ge \varphi(a_S, b_S) = \left(a_S + \tfrac12\right)^2 + \left(b_S + \tfrac12\right)^2 \ge \tfrac14 + \tfrac14 = \tfrac12 . \qquad \square
```

*Lean: [`half_le_phi`](../../SquaresInCircles/One/Optimality.lean#L13),
[`One.squared_lower`](../../SquaresInCircles/One/Optimality.lean#L17),
[`One.optimality`](../../SquaresInCircles/One/Optimality.lean#L21).*

## Uniqueness

### Proposition 1.3 (uniqueness)

If a unit square $S$ lies in the closed disk of radius $\frac{\sqrt2}2$ about
$o$, then $c_S = o$, and the packing has the normal form of $(0, 0)$.

*Proof.* At $R^2 = \frac12$ both inequalities in the proof of
Proposition 1.2 are equalities, so $a_S = b_S = 0$, and by Lemma 1
$|c_S - o|^2 = a_S^2 + b_S^2 = 0$. In the frame of its own first axis, $S$ then
sits at $(0, 0)$ ([Lemma 21](common.md#lemma-21-sitting-at-a-centre)), and
[Lemma 22](common.md#lemma-22-from-slots-to-a-normal-form) gives the normal
form. $\square$

*Lean: [`One.uniqueness`](../../SquaresInCircles/One/Uniqueness.lean#L9).*