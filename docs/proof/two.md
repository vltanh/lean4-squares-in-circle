# Two squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 2.** Let $R_2 = \frac{\sqrt5}2$.

1. The squares $Q(-\frac12, 0)$ and $Q(\frac12, 0)$ form a packing in the
   closed disk of radius $R_2$ about the origin.
2. A packing of two unit squares in a closed disk of radius $R$ forces
   $R \ge R_2$.
3. A packing of two unit squares in a closed disk of radius $R_2$ has the
   normal form of $(-\frac12, 0), (\frac12, 0)$: the squares form a
   $2 \times 1$ rectangle centred at the disk centre.

![Two unit squares side by side forming a 2 by 1 rectangle centred at o, with its four corners on the dashed circle of radius root 5 over 2](figures/two.svg)

*Two squares. The corners of the $2 \times 1$ rectangle lie on the circle of
radius $R_2$.*

*Sketch.* In a disk of radius below $R_2$, the farthest-vertex bound keeps both
centres within $\frac12$ of the disk centre, so they are less than 1 apart.
Disjoint unit squares cannot be that close.

*Lean: [`Two.attainment`](../../SquaresInCircles/Two/Construction.lean#L36),
[`Two.optimality`](../../SquaresInCircles/Two/Optimality.lean#L52),
[`Two.uniqueness`](../../SquaresInCircles/Two/Uniqueness.lean#L10), in
[`SquaresInCircles/Two/`](../../SquaresInCircles/Two).*

## Construction

### Proposition 2.1 (attainment)

$Q(-\frac12, 0)$ and $Q(\frac12, 0)$ are disjoint and lie in the closed disk
of radius $\frac{\sqrt5}2$ about the origin.

*Proof.* The centres differ by 1 in the first coordinate, and both squares lie
in $[-1, 1] \times [-\frac12, \frac12]$, with $1 + \frac14 = \frac54$. Apply
[Lemma 20](common.md#lemma-20-axis-parallel-squares). $\square$

*Lean: [`Two.model_disjoint`](../../SquaresInCircles/Two/Construction.lean#L25),
[`Two.model_packing`](../../SquaresInCircles/Two/Construction.lean#L30),
[`Two.attainment`](../../SquaresInCircles/Two/Construction.lean#L36).*

## Lower bound

### Lemma 2.2 (centres near the disk centre)

If $a, b \ge 0$ and $\varphi(a, b) < \frac54$, then $a^2 + b^2 < \frac14$.
The same holds with $\le$ in both places.

*Proof.* Expanding,

```math
\varphi(a, b) = (a^2 + b^2) + (a + b) + \tfrac12 .
```

If $a^2 + b^2 \ge \frac14$, then $(a + b)^2 \ge a^2 + b^2 \ge \frac14$, so
$a + b \ge \frac12$ and $\varphi(a, b) \ge \frac14 + \frac12 + \frac12 = \frac54$.
The version with $\le$ is the same argument. $\square$

*Lean:
[`center_near_of_phi_lt`](../../SquaresInCircles/Two/Optimality.lean#L25),
[`center_near_of_phi_le`](../../SquaresInCircles/Two/Optimality.lean#L18).*

### Proposition 2.3 (lower bound)

If two disjoint unit squares lie in the closed disk of radius $R$ about $o$,
then $R^2 \ge \frac54$.

![Two centres c_S and c_T inside the dashed disk of radius one half about o, the parallelogram with vertices o, c_S, c_S plus c_T minus o, and c_T, and its two diagonals](figures/parallelogram.svg)

*The parallelogram spanned by $c_S - o$ and $c_T - o$. Its squared diagonals add
up to twice the squared sides from $o$, so if both centres are within $\frac12$
of $o$, the diagonal from $c_S$ to $c_T$ is shorter than 1.*

*Proof.* Suppose $R^2 < \frac54$, and call the squares $S$ and $T$. By
[Lemma 1](common.md#lemma-1-farthest-vertex) and Lemma 2.2, applied to
$(a_S, b_S)$ and to $(a_T, b_T)$, both centres are within $\frac12$ of $o$.
The parallelogram law

```math
|c_S - c_T|^2 + |c_S + c_T - 2o|^2 = 2|c_S - o|^2 + 2|c_T - o|^2 < 1
```

then gives $|c_S - c_T| < 1$, which contradicts
[Lemma 4](common.md#lemma-4-centres-at-least-1-apart). $\square$

*Lean: [`normSq_parallelogram`](../../SquaresInCircles/Two/Optimality.lean#L33),
[`Two.squared_lower`](../../SquaresInCircles/Two/Optimality.lean#L39),
[`Two.optimality`](../../SquaresInCircles/Two/Optimality.lean#L52).*

## Uniqueness

### Proposition 2.4 (uniqueness)

If two disjoint unit squares lie in the closed disk of radius
$\frac{\sqrt5}2$ about $o$, the packing has the normal form of
$(-\frac12, 0), (\frac12, 0)$.

*Proof.*

1. *The disk centre is the midpoint.* By Lemma 2.2 with $\le$, the
   parallelogram law now bounds $|c_S - c_T|^2 + |c_S + c_T - 2o|^2$ by 1.
   With $|c_S - c_T| \ge 1$ this forces $|c_S - c_T| = 1$ and
   $c_S + c_T = 2o$.
2. *The squares share an edge.* By
   [Lemma 6](common.md#lemma-6-squares-at-distance-1) their sides are parallel
   and $c_T - c_S$ is $\pm e^S_1$ or $\pm e^S_2$.
3. *The rectangle.* In the frame of $S$ the squares sit at
   $\mp\frac12(c_T - c_S)$
   ([Lemma 21](common.md#lemma-21-sitting-at-a-centre)), that is at
   $(\mp\frac12, 0)$ or at $(0, \mp\frac12)$. In the second case a quarter
   turn of the frame gives $(\pm\frac12, 0)$.
   [Lemma 22](common.md#lemma-22-from-slots-to-a-normal-form) gives the normal
   form. $\square$

*Lean: [`Two.uniqueness`](../../SquaresInCircles/Two/Uniqueness.lean#L10).*