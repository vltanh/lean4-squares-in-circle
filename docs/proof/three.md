# Three squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 3.** Let $R_3 = \frac{5\sqrt{17}}{16}$, and let
$c_1 = (-\frac12, -\frac5{16})$, $c_2 = (\frac12, -\frac5{16})$,
$c_3 = (0, \frac{11}{16})$.

1. $Q(c_1), Q(c_2), Q(c_3)$ form a packing in the closed disk of radius $R_3$
   about the origin: the T, two squares side by side and a third centred on
   top of them.
2. A packing of three unit squares in a closed disk of radius $R$ forces
   $R \ge R_3$.
3. A packing of three unit squares in a closed disk of radius $R_3$ has the
   normal form of $c_1, c_2, c_3$.

![The T packing in its dashed circle of radius 5 root 17 over 16, with the small circle of radius 3/8 about the centre divided into three coloured arcs of 120 degrees, one in each square](figures/three.svg)

*The T. The small circle $\Gamma_{3/8}$ about the disk centre $o$
splits into three arcs of exactly 120°, one in each square.*

*Sketch.* Draw the small circle $\Gamma_{3/8}$ about the disk centre. In a disk
of radius below $R_3$, every square that avoids the centre holds more than a
third of that circle, so the three squares cannot all avoid it. If one square
contains the centre, the arcs are so tight that the other two are forced into
nearly the T position, where they overlap. At radius exactly $R_3$ every
inequality is tight, and only the T is left.

*Lean: [`Three.attainment`](../../SquaresInCircles/Three/Construction.lean#L42),
[`Three.optimality`](../../SquaresInCircles/Three/Optimality.lean#L36),
[`Three.uniqueness`](../../SquaresInCircles/Three/Uniqueness.lean#L289), in
[`SquaresInCircles/Three/`](../../SquaresInCircles/Three).*

## Construction

### Proposition 3.1 (attainment)

$Q(c_1), Q(c_2), Q(c_3)$ are pairwise disjoint and lie in the closed disk of
radius $R_3$ about the origin.

*Proof.* Any two of the centres differ by at least 1 in one coordinate. The
lower squares lie in the box $[-1, 1] \times [-\frac{13}{16}, \frac{13}{16}]$,
the upper one in $[-\frac12, \frac12] \times [-\frac{19}{16}, \frac{19}{16}]$,
and

```math
1 + \tfrac{169}{256} = \tfrac14 + \tfrac{361}{256} = \tfrac{425}{256} = R_3^2 .
```

Apply [Lemma 20](common.md#lemma-20-axis-parallel-squares). $\square$

The six outer corners, $(\pm1, -\frac{13}{16})$ and
$(\pm\frac12, \frac{19}{16})$, lie on the circle.

*Lean:
[`Three.model_disjoint`](../../SquaresInCircles/Three/Construction.lean#L27),
[`Three.model_packing`](../../SquaresInCircles/Three/Construction.lean#L32),
[`Three.attainment`](../../SquaresInCircles/Three/Construction.lean#L42).*

## Lower bound

### Proposition 3.2 (lower bound)

If three pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R^2 \ge \frac{425}{256}$.

The proof takes four steps.

1. **The contact polygon.** A smaller disk puts $(a_S, b_S)$ strictly inside a
   16-gon $P_3$ for every square $S$.
2. **Exterior squares.** Each square that avoids $o$ then holds more than a
   third of the circle $\Gamma_{3/8}$. So some square contains $o$.
3. **The containing square.** A square containing $o$ leaves the other two
   too little room.
4. **Conclusion.**

*Lean:
[`Three.squared_lower`](../../SquaresInCircles/Three/Optimality.lean#L27),
[`Three.optimality`](../../SquaresInCircles/Three/Optimality.lean#L36).*

### Step 1. The contact polygon

#### Definition 3.3 (the 16-gon)

$P_3$ is the set of points $(a, b)$ with

```math
\begin{aligned}
16a + 13b &\le \tfrac{193}{16}, & 13a + 16b &\le \tfrac{193}{16}, \\
19a + 8b &\le \tfrac{209}{16}, & 8a + 19b &\le \tfrac{209}{16}.
\end{aligned}
```

These are the tangent half-planes of $\varphi = \frac{425}{256}$ at
$(\frac12, \frac5{16})$, at $(\frac{11}{16}, 0)$, and at their mirror images.
In the T, the two lower squares have $(a_S, b_S) = (\frac12, \frac5{16})$ and
the upper one has $(a_S, b_S) = (\frac{11}{16}, 0)$.

![The part with a, b at least 0 of the 16-gon P3 in the (a, b)-plane, hugging the disk where phi is at most 425/256; the disk touches it at the points A, (11/16, 0) and (0, 11/16), and B, (1/2, 5/16) and (5/16, 1/2)](figures/sixteen-gon.svg)

*The 16-gon $P_3$ where $a, b \ge 0$. It touches the disk
$\lbrace \varphi \le \frac{425}{256} \rbrace$ at the positions of the squares of
the T, marked with their types (Lemma 3.5).*

*Lean: [`P3`](../../SquaresInCircles/Three/Tangents.lean#L12),
[`P3Strict`](../../SquaresInCircles/Three/Tangents.lean#L16).*

#### Lemma 3.4 (contact polygon)

1. If $\varphi(a, b) < \frac{425}{256}$, then $(a, b)$ is strictly inside
   $P_3$. If $\varphi(a, b) \le \frac{425}{256}$, then $(a, b) \in P_3$.
2. If $a, b \ge 0$ and $(a, b) \in P_3$, then $a, b \le \frac{11}{16}$.

*Proof.* (1) is [Lemma 2](common.md#lemma-2-tangent-lines) at the four tangent
points. (2) follows from $19a + 8b \le \frac{209}{16}$ and its mirror image.
$\square$

From here on the lower bound uses only the polygon and disjointness; the disk
is not needed again.

*Lean: [`p3_of_phi_lt`](../../SquaresInCircles/Three/Tangents.lean#L27),
[`p3_of_phi_le`](../../SquaresInCircles/Three/Tangents.lean#L20),
[`p3_coordinates`](../../SquaresInCircles/Three/Tangents.lean#L34).*

### Step 2. Exterior squares

#### Lemma 3.5 (exterior caps)

Let $S$ be exterior with $(a_S, b_S) \in P_3$. Then $S$ holds a cap of
$\Gamma_{3/8}$ of length at least $\frac{2\pi}3$. The length is exactly
$\frac{2\pi}3$ only in two cases:

- $(a_S, b_S) = (\frac{11}{16}, 0)$, *type A*: $o$ lies on an axis of $S$;
- $(a_S, b_S) = (\frac12, \frac5{16})$, *type B*: $o$ lies on the line of an
  edge of $S$.

These are the two kinds of square in the T.

![Left: a type A square in its chart, centred on the axis through o, holding a third of the circle of radius 3/8. Right: a type B square with o on the line of its left edge, holding a third of that circle and half of the circle of radius 1/16](figures/contact-types.svg)

*The two tight cases, each in its chart. Each square holds exactly a third of
$\Gamma_{3/8}$. The type B square also holds half of $\Gamma_{1/16}$, which
uniqueness uses (Lemma 3.14).*

*Idea.* The 16-gon keeps $S$ close enough to $o$ that the cap of
[Lemma 13](common.md#lemma-13-the-cap) is long. The two terms of the cap
length are each at least $\frac{2\pi}3$, and each is tight for one type.

*Proof.* Put

```math
u_S = \frac{a_S - \frac12}{3/8}, \qquad v_S = \frac{\frac12 - b_S}{3/8}, \qquad A_S = \arccos u_S, \qquad V_S = \arcsin v_S .
```

The polygon gives three facts:

- $a_S \le \frac{11}{16}$ (Lemma 3.4), that is $u_S \le \frac12$;
- the facet $16a + 13b \le \frac{193}{16}$ at $(a_S, b_S)$ rewrites exactly as
  $v_S \ge \frac12 + \frac{16}{13}u_S$;
- the same facet with $a_S \ge \frac12$ gives $b_S \le \frac5{16}$.

So Lemma 13 applies, and the cap has length $\min(2A_S, A_S + V_S)$. Both
terms are at least $\frac{2\pi}3$:

- $u_S \le \frac12$ means $A_S \ge \frac\pi3$, so $2A_S \ge \frac{2\pi}3$.
- $A_S + V_S \ge \frac{2\pi}3$ says $\arcsin v_S \ge \arcsin u_S + \frac\pi6$,
  since $A_S = \frac\pi2 - \arcsin u_S$. This holds because

```math
\sin\left(\arcsin u_S + \tfrac\pi6\right) = \tfrac{\sqrt3}2\,u_S + \tfrac12\sqrt{1 - u_S^2}
\le \tfrac12 + u_S \le \tfrac12 + \tfrac{16}{13}u_S \le v_S .
```

*Equality.* If $2A_S = \frac{2\pi}3$, then $u_S = \frac12$, so
$a_S = \frac{11}{16}$, and the facet $19a + 8b \le \frac{209}{16}$ leaves
$b_S = 0$: type A. If $A_S + V_S = \frac{2\pi}3$, the chain above is tight.
Its middle step $u_S \le \frac{16}{13}u_S$ is tight only at $u_S = 0$, and
then $v_S = \frac12$: $(a_S, b_S) = (\frac12, \frac5{16})$, type B. $\square$

*Lean: [`three_cap_data`](../../SquaresInCircles/Three/Exterior.lean#L66),
[`three_truncated_gap`](../../SquaresInCircles/Three/Exterior.lean#L34),
[`three_cap_contact_types`](../../SquaresInCircles/Three/Exterior.lean#L82),
[`three_cap_arc_formula`](../../SquaresInCircles/Three/Exterior.lean#L101).*

#### Corollary 3.6 (a containing square)

If three pairwise disjoint squares $S$ all have $(a_S, b_S)$ strictly inside
$P_3$, exactly one of them contains $o$.

*Proof.* Both types lie on the boundary of $P_3$: type A on
$19a + 8b = \frac{209}{16}$, type B on $16a + 13b = \frac{193}{16}$. So by
Lemma 3.5 every exterior square holds an arc of half-width more than
$\frac\pi3$. Three such arcs would break the angular budget,
[Lemma 7](common.md#lemma-7-angular-budget). And two disjoint squares cannot
both contain $o$. $\square$

*Lean: [`three_exterior_arc`](../../SquaresInCircles/Three/Exterior.lean#L109),
[`three_exterior_reduction`](../../SquaresInCircles/Three/Exterior.lean#L126).*

### Step 3. The containing square

This step rules out a square containing $o$. It is the hardest part of the
whole project; the radial sweep that handles four and five squares gives too
short an arc here.

*Idea.* The containing square $S$ holds a quarter of $\Gamma_{3/8}$ and a bit
more. Each of the other two squares holds at least a third. So the three arcs
nearly fill the circle, and the slack $\delta$ is less than $\frac1{12}$. That
leaves no freedom:

- neither of the other caps can be clipped, or it alone would use up the
  slack (Lemma 3.9);
- both caps are nearly exactly 120° and symmetric about their squares'
  phases, so both squares are nearly of type A;
- their phases are between $\frac{2\pi}3$ and $\frac{2\pi}3 + \frac1{12}$ apart,
  and two such squares overlap (Lemma 3.10).

Throughout this step, $S$ contains $o$, so $b_S \le a_S < \frac12$. Put

```math
P_S = \frac{\frac12 - a_S}{3/8}, \qquad Q_S = \frac{\frac12 - b_S}{3/8}, \qquad 0 < P_S \le Q_S .
```

(As in mathlib, $\arcsin x = \frac\pi2$ for $x \ge 1$.)

#### Lemma 3.7 (the arc of a containing square)

$S$ holds an arc of $\Gamma_{3/8}$ of length

```math
L_S = \tfrac\pi2 + \arcsin P_S + \arcsin Q_S .
```

![A square containing o in its chart, centred at (a_S, b_S), and the highlighted arc of the circle of radius 3/8 inside it, running from its lower edge round to its left edge](figures/containing-arc.svg)

*The arc of length $L_S$ runs from the lower edge of $S$ round to its left edge;
the far edges are out of reach.*

*Proof.* In the chart of $S$, the circle point at angle $t$ is
$(\frac38\cos t, \frac38\sin t)$. It lies in $S$ as soon as $\cos t > -P_S$
and $\sin t > -Q_S$, because the far edges, at $a_S + \frac12$ and
$b_S + \frac12$, are out of reach. Both hold for
$-\arcsin Q_S < t < \frac\pi2 + \arcsin P_S$, an interval of length $L_S$, and
[Lemma 10](common.md#lemma-10-charts) (2) turns it into an arc. $\square$

The arc is the quarter circle facing the centre of $S$, extended a little on
each side.

*Lean:
[`three_containing_mem`](../../SquaresInCircles/Three/Containing.lean#L140),
[`three_containing_arc_formula`](../../SquaresInCircles/Three/Containing.lean#L177).*

#### Lemma 3.8 (the radial gap)

Let $T$ be disjoint from $S$, with $(a_T, b_T) \in P_3$. Then

```math
\tfrac12 - a_S \le a_T - \tfrac12 .
```

That is: the near edge of $T$ is at least as far from $o$ as the inscribed disk
of $S$ about $o$ reaches.

![A containing square S with the shaded disk of radius one half minus a_S about o inside it, and a square T to its right; below, the radius of the disk and the distance from o to the near edge of T are compared](figures/radial-gap.svg)

*In the frame $\theta_T$. The disk of radius $\frac12 - a_S$ about $o$ lies in
$S$, so the near edge of $T$, at distance $a_T - \frac12$ from $o$, cannot come
closer.*

*Proof.* $T$ is exterior, so $a_T \ge \frac12$, and then the facet
$16a + 13b \le \frac{193}{16}$ at $(a_T, b_T)$ gives $b_T \le \frac5{16}$.

- Both local coordinates of $o$ in $S$ are at most $a_S$, so the open disk of
  radius $\frac12 - a_S$ about $o$ lies in $S$
  ([Lemma 3](common.md#lemma-3-inscribed-disks) (2)).
- Suppose $a_T - \frac12 < \frac12 - a_S$, and pick $\rho$ strictly between.
  The point at distance $\rho$ from $o$ in the direction $\theta_T$ has
  coordinates $(\rho, 0)$ in the frame $\theta_T$, where $T$ is the unit square
  centred at $(a_T, \pm b_T)$
  ([Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart)). Since
  $|\rho - a_T| < \frac12$ and $b_T < \frac12$, the point lies in $T$.
- It also lies in the disk inside $S$, a contradiction. $\square$

*Lean:
[`three_gap_from_containing`](../../SquaresInCircles/Three/Containing.lean#L197).*

#### Lemma 3.9 (an increasing difference)

The function

```math
f(t) = \arcsin\left(\tfrac12 + \tfrac{16}{13}t\right) - \arcsin t
```

is increasing on every interval $[t_0, t_1]$ with $t_0 \ge 0$ and
$\frac12 + \frac{16}{13}t_1 < 1$.

*Proof.* On such an interval $0 \le t < \frac12 + \frac{16}{13}t < 1$. So the
first square root below is the smaller one, and

```math
f'(t) = \frac{16/13}{\sqrt{1 - \left(\frac12 + \frac{16}{13}t\right)^2}} - \frac1{\sqrt{1 - t^2}} > 0 . \qquad \square
```

*Lean:
[`three_asin_increment_mono`](../../SquaresInCircles/Three/Containing.lean#L28).*

#### Lemma 3.10 (two nearly axial squares overlap)

Let $T$ and $U$ satisfy $\frac12 \le a_T, a_U \le \frac{11}{16}$ and
$b_T, b_U < \frac1{16}$, and let their phases satisfy

```math
\tfrac{2\pi}3 \le d(\theta_T, \theta_U) < \tfrac{2\pi}3 + \tfrac1{12} .
```

Then $T$ and $U$ are not disjoint.

![Two squares T and U whose axes pass close to o, in directions an angle Delta apart; their overlap is shaded and contains the point z](figures/near-axis-overlap.svg)

*With $\Delta$ a little over $\frac{2\pi}3$, the squares overlap near $o$. The
point $z = (\frac15, \frac25)$ of the frame $\theta_T$ lies in both.*

*Proof.* Let $\Delta = d(\theta_T, \theta_U)$. The bounds on $\Delta$ give

```math
-\tfrac35 < \cos\Delta \le -\tfrac12, \qquad \tfrac45 < |\sin\Delta| < \tfrac78 .
```

In the frame $\theta_T$, $T$ is the unit square centred at $(a_T, \pm b_T)$
(Lemma 11), and $U$ is the same kind of square in the frame turned by
$\pm\Delta$. Take the point $(\frac15, \frac25)$ in the frame $\theta_T$,
with the sign of the second coordinate matching the turn.

- It lies in $T$, because $\frac12 \le a_T \le \frac{11}{16}$ and
  $b_T < \frac1{16}$.
- In the frame $\theta_U$ its coordinates are

```math
\left(\tfrac15\cos\Delta + \tfrac25|\sin\Delta|,\ \ \tfrac25\cos\Delta - \tfrac15|\sin\Delta|\right) \in \left(\tfrac15, \tfrac14\right) \times \left(-\tfrac{83}{200}, -\tfrac9{25}\right),
```

  which is within $\frac12$ of the centre $(a_U, \pm b_U)$ of $U$ in both
  coordinates. So it lies in $U$ as well. $\square$

*Lean: [`near_axis_angles`](../../SquaresInCircles/Three/Containing.lean#L257),
[`near_axis_square_overlap`](../../SquaresInCircles/Three/Containing.lean#L301).*

#### Proposition 3.11 (the containing square)

Let $S$ contain $o$ with $(a_S, b_S)$ strictly inside $P_3$, and let $T$ and
$U$ have $(a_T, b_T), (a_U, b_U) \in P_3$. Then $S$, $T$, $U$ are not pairwise
disjoint.

Only $S$ needs the strict polygon. That lets uniqueness reuse this
proposition.

*Proof.* Suppose they are pairwise disjoint. Then $T$ and $U$ are exterior.
Define $u_T, v_T, A_T, V_T$ for $T$ as in the proof of Lemma 3.5, and likewise
for $U$.

**(a) The slack is small.** By Lemma 3.5 the caps of $T$ and $U$ are at least
$\frac{2\pi}3$ long, and by Lemma 3.7 the arc of $S$ is $L_S$ long. The
three-arc budget ([Lemma 9](common.md#lemma-9-three-arcs)) gives
$L_S \le \frac{2\pi}3$. Write the slack as

```math
\delta = \tfrac{2\pi}3 - L_S = \tfrac\pi6 - \arcsin P_S - \arcsin Q_S \ge 0 .
```

The strict facet $16a + 13b < \frac{193}{16}$ at $(a_S, b_S)$ says

```math
\tfrac{16}{13}P_S + Q_S > \tfrac12 ;
```

call this inequality $(\ast)$. With $P_S \le Q_S$ it gives
$P_S + Q_S > \frac{13}{29}$. Using $\arcsin x \ge x$ and $\pi < \frac{22}7$
([Lemma 19](common.md#lemma-19-elementary-estimates)),

```math
\delta < \tfrac{11}{21} - \tfrac{13}{29} < \tfrac1{12} .
```

**(b) No cap is clipped.** Suppose the cap of $T$ is clipped, $V_T < A_T$. Its
length is then $A_T + V_T = \frac\pi2 - \arcsin u_T + \arcsin v_T$, where
$v_T \ge \frac12 + \frac{16}{13}u_T$ (as in Lemma 3.5) and $v_T < 1$. By
Lemma 3.8, $u_T \ge P_S$, so Lemma 3.9 on $[P_S, u_T]$ gives
$\arcsin v_T - \arcsin u_T \ge f(u_T) \ge f(P_S)$. Adding the arc of $S$:

```math
(A_T + V_T) + L_S \ge \pi + \arcsin\left(\tfrac12 + \tfrac{16}{13}P_S\right) + \arcsin Q_S > \pi + \tfrac\pi3 ,
```

by Lemma 19 (4) with $\theta = \frac\pi6$: by $(\ast)$ the two arguments
average more than $\frac12 = \sin\frac\pi6$. With the cap of $U$, at least
$\frac{2\pi}3$, the three arcs would exceed $2\pi$. The same holds for $U$. So
both caps are full, $A_T \le V_T$ and $A_U \le V_U$, and each is centred at its
square's phase (Lemma 13).

**(c) Both squares are nearly of type A.** The full cap of $T$ has length
$2A_T$, and the budget gives $2A_T \le 2\pi - L_S - \frac{2\pi}3 = \frac{2\pi}3 + \delta$.
So $A_T = \frac\pi3 + \eta$ with $0 \le \eta < \frac1{24}$, and

```math
u_T = \cos A_T = \tfrac12\cos\eta - \tfrac{\sqrt3}2\sin\eta \ge \tfrac12\left(1 - \tfrac{\eta^2}2\right) - \eta > \tfrac9{20} .
```

Hence $a_T > \frac12 + \frac9{20}\cdot\frac38 = \frac{107}{160}$, and the facet
$19a + 8b \le \frac{209}{16}$ at $(a_T, b_T)$ leaves $b_T < \frac1{16}$. Also
$a_T \le \frac{11}{16}$ by Lemma 3.4. The same holds for $U$.

**(d) Their phases are about 120° apart.** The caps of $T$ and $U$ are
centred at $\theta_T$ and $\theta_U$, with half-widths $A_T, A_U \ge \frac\pi3$.
Lemma 9, with the arc of $S$ as the third arc, gives

```math
\tfrac{2\pi}3 \le A_T + A_U \le d(\theta_T, \theta_U) \le 2\pi - L_S - A_T - A_U \le \tfrac{2\pi}3 + \delta < \tfrac{2\pi}3 + \tfrac1{12} .
```

**(e) They overlap.** By (c) and (d), Lemma 3.10 applies to $T$ and $U$, which
contradicts their disjointness. $\square$

*Lean:
[`three_deficit_bounds`](../../SquaresInCircles/Three/Containing.lean#L91),
[`three_compensation`](../../SquaresInCircles/Three/Containing.lean#L74),
[`three_cap_near_axis`](../../SquaresInCircles/Three/Containing.lean#L109),
[`three_cap_reduction`](../../SquaresInCircles/Three/Containing.lean#L228),
[`three_containing_impossible`](../../SquaresInCircles/Three/Containing.lean#L333).*

### Step 4. Conclusion

#### Proposition 3.12 (polygon relaxation)

No three pairwise disjoint squares $S$ all have $(a_S, b_S)$ strictly inside
$P_3$.

*Proof.* By Corollary 3.6 one of them contains $o$, and Proposition 3.11 rules
that out. $\square$

*Lean:
[`three_polygon_strict_impossible`](../../SquaresInCircles/Three/Optimality.lean#L21).*

*Proof of Proposition 3.2.* If $R^2 < \frac{425}{256}$, then by
[Lemma 1](common.md#lemma-1-farthest-vertex) and Lemma 3.4, $(a_S, b_S)$ is
strictly inside $P_3$ for every square $S$, which Proposition 3.12 excludes.
$\square$

## Uniqueness

*Idea.* At radius exactly $R_3$, rerun the argument with equality allowed. A
containing square is still impossible, so all three caps exist, and they must
be exactly 120° each. That makes every square type A or type B, and the
angles between the arcs fix the T.

### Lemma 3.13 (a containing square is strictly inside)

If $a, b < \frac12$ and $\varphi(a, b) \le \frac{425}{256}$, then $(a, b)$ is
strictly inside $P_3$.

*Proof.* $(a, b)$ is neither $(\frac12, \frac5{16})$ nor
$(\frac5{16}, \frac12)$, so the square terms in Lemma 2 are positive there,
and the tangents at these two points hold strictly. With $a < \frac12$, the
strict facet $16a + 13b < \frac{193}{16}$ gives $19a + 8b < \frac{209}{16}$,
and symmetrically for the fourth facet. $\square$

*Lean:
[`tangent_strict_of_ne`](../../SquaresInCircles/Three/Uniqueness.lean#L22),
[`p3_strict_of_inside`](../../SquaresInCircles/Three/Uniqueness.lean#L32).*

### Lemma 3.14 (arcs of the two types)

Let $S$ have phase $\theta_S$ and sign $\varepsilon_S$.

1. If $S$ is of type A, it holds an arc of $\Gamma_{3/8}$ of half-width
   $\frac\pi3$ centred at $\theta_S$.
2. If $S$ is of type B, it holds an arc of $\Gamma_{1/16}$ of half-width
   $\frac\pi2$ (a semicircle) centred at $\theta_S$, and an arc of
   $\Gamma_{3/8}$ of half-width $\frac\pi3$ centred at
   $\theta_S + \varepsilon_S\frac\pi6$.

Both arcs are drawn in the figure of [Lemma 3.5](#lemma-35-exterior-caps).

*Proof.* We give the chart angles; [Lemma 10](common.md#lemma-10-charts) (2)
turns them into arcs.

1. For $|t| < \frac\pi3$: $\frac38\cos t > \frac3{16} = a_S - \frac12$, and
   $|\frac38\sin t| < \frac12$.
2. For $|t| < \frac\pi2$: $\frac1{16}\cos t > 0 = a_S - \frac12$ and
   $|\frac1{16}\sin t - \frac5{16}| < \frac12$. For
   $-\frac\pi6 < t < \frac\pi2$: $\frac38\cos t > 0$ and
   $\frac38\sin t > -\frac3{16} = b_S - \frac12$. This interval has half-width
   $\frac\pi3$ and midpoint $\frac\pi6$. $\square$

*Lean: [`a_contact_arc`](../../SquaresInCircles/Three/Uniqueness.lean#L45),
[`b_semicircle`](../../SquaresInCircles/Three/Uniqueness.lean#L63),
[`b_contact_arc`](../../SquaresInCircles/Three/Uniqueness.lean#L76).*

### Proposition 3.15 (uniqueness)

If three pairwise disjoint unit squares lie in the closed disk of radius $R_3$
about $o$, the packing has the normal form of $c_1, c_2, c_3$.

*Proof.* Every square $S$ has $(a_S, b_S) \in P_3$ by Lemma 3.4.

**(1) No square contains $o$.** A containing square $S$ has
$(a_S, b_S)$ strictly inside $P_3$ by Lemma 3.13, and that is all
Proposition 3.11 asks of it.

**(2) Every cap is exactly 120°.** All three squares are exterior, each cap
is at least $\frac{2\pi}3$ (Lemma 3.5), and together they are at most $2\pi$
(Lemma 7). So each is exactly $\frac{2\pi}3$, and each square is of type A or
type B.

**(3) One square of type A, two of type B.**

- Two type A squares: by Lemma 3.14 (1) and Lemma 9 their phases are exactly
  $\frac{2\pi}3$ apart, and Lemma 3.10 makes them overlap.
- Three type B squares: they would hold three disjoint semicircles of
  $\Gamma_{1/16}$ (Lemma 3.14 (2)), against Lemma 9.

**(4) The angles.** Call the type B squares $S_1, S_2$ and the type A square
$S_3$, and write $\theta_i = \theta_{S_i}$ and $\varepsilon_i = \varepsilon_{S_i}$.

- The two B-semicircles on $\Gamma_{1/16}$ are disjoint, so their centres are
  $\pi$ apart ([Lemma 8](common.md#lemma-8-disjoint-arcs-have-separated-centres)):
  $\theta_2 = \theta_1 + \pi$.
- On $\Gamma_{3/8}$ the three squares hold arcs of half-width $\frac\pi3$
  centred at $\theta_1 + \varepsilon_1\frac\pi6$,
  $\theta_2 + \varepsilon_2\frac\pi6$ and $\theta_3$. They fill the circle, so
  by Lemma 9 their centres are pairwise exactly $\frac{2\pi}3$ apart.
- If $\varepsilon_1 = \varepsilon_2$, the first two centres would be $\pi$
  apart. So $\varepsilon_2 = -\varepsilon_1$, and the two remaining conditions

  ```math
  \cos\left(\theta_3 - \theta_1 - \varepsilon_1\tfrac\pi6\right) = -\tfrac12, \qquad
  \cos\left(\theta_3 - \theta_1 - \pi + \varepsilon_1\tfrac\pi6\right) = -\tfrac12
  ```

  subtract to $\sin(\theta_3 - \theta_1) = -\varepsilon_1$, that is
  $\theta_3 = \theta_1 - \varepsilon_1\frac\pi2$.

**(5) The T.** Read off the centres with Lemma 11 in the frame $\theta_1$:

| square | phase | sits at |
| --- | --- | --- |
| $S_1$ (type B) | $\theta_1$ | $(\frac12, \frac5{16}\varepsilon_1)$ |
| $S_2$ (type B) | $\theta_1 + \pi$, sign $-\varepsilon_1$ | $(-\frac12, \frac5{16}\varepsilon_1)$ |
| $S_3$ (type A) | $\theta_1 - \varepsilon_1\frac\pi2$ | $(0, -\frac{11}{16}\varepsilon_1)$ |

For $\varepsilon_1 = -1$ these are $c_2, c_1, c_3$. For $\varepsilon_1 = 1$ a
half-turn of the frame gives them
([Lemma 21](common.md#lemma-21-sitting-at-a-centre) (2)).
[Lemma 22](common.md#lemma-22-from-slots-to-a-normal-form) gives the normal
form. $\square$

*Lean:
[`three_no_containing`](../../SquaresInCircles/Three/Uniqueness.lean#L260),
[`two_a_contacts_impossible`](../../SquaresInCircles/Three/Uniqueness.lean#L107),
[`three_b_contacts_impossible`](../../SquaresInCircles/Three/Uniqueness.lean#L124),
[`equilateral_arc_centers`](../../SquaresInCircles/Three/Uniqueness.lean#L95),
[`apex_phase`](../../SquaresInCircles/Three/Uniqueness.lean#L139),
[`t_contact_reconstruction`](../../SquaresInCircles/Three/Uniqueness.lean#L184),
[`Three.uniqueness`](../../SquaresInCircles/Three/Uniqueness.lean#L289).*

## The legacy certificate proof

The first formalization of this case is on the
[`legacy`](https://github.com/vltanh/lean4-squares-in-circles/tree/legacy)
branch, with its own README and axiom audit. It normalizes a packing into a
fixed angle triangle, extracts separating axes, eliminates directed-chain
patterns to leave 48 branches, and bounds a trigonometric polynomial on each
branch with 53 rational certificates checked by `decide +kernel`. Its
`Cert.optimality` proves the lower bound of `Three.optimality`, stated with
that branch's `Packing` for `Fin 3` and its constant `optimalRadius`.

The occupied-arc proof above replaced it as the main proof. One framework
covers three, four and five squares and extends to uniqueness, with no case
enumeration and no certificate tables.
