# Seven squares

[Back to the proof overview](README.md) · [Preliminaries](preliminaries.md) · [Shared lemmas](common.md)

**Theorem 7.** Let $R_7 = \frac{\sqrt{13}}2$, and let $c_1, \dots, c_7$ be the
points $(1, -\frac12)$, $(1, \frac12)$, $(-1, -\frac12)$, $(-1, \frac12)$,
$(0, -1)$, $(0, 0)$, $(0, 1)$.

1. $Q(c_1), \dots, Q(c_7)$ form a packing in the closed disk of radius $R_7$
   about the origin: a column of three squares between two columns of two.
   More generally the middle column can slide: for any $y_1, y_2, y_3$ with
   $y_1 + 1 \le y_2$, $y_2 + 1 \le y_3$ and
   $-(\sqrt3 - \frac12) \le y_1$, $y_3 \le \sqrt3 - \frac12$, the squares
   $Q(\pm1, \pm\frac12)$, $Q(0, y_1)$, $Q(0, y_2)$, $Q(0, y_3)$ form such a
   packing.
2. A packing of seven unit squares in a closed disk of radius $R$ forces
   $R \ge R_7$.
3. A packing of seven unit squares in a closed disk of radius $R_7$ has the
   normal form of $(\pm1, \pm\frac12)$, $(0, y_1)$, $(0, y_2)$, $(0, y_3)$
   for some $y_1, y_2, y_3$ as in (1).

So the optimum is not unique: by (1) the optimal packings form a
three-parameter family, with infinitely many packings that no rotation and
relabelling carry onto one another. By (3) there are no others.

![The packing of seven squares in its dashed circle of radius root 13 over 2: a grey middle square around the centre, one square above and one below it, and two squares on either side; the unit circle about the centre is divided into six coloured arcs of 60 degrees, one in each square other than the middle one](figures/seven.svg)

*Seven squares. The unit circle $\Gamma_1$ about the disk centre $o$ splits
into six arcs of exactly 60°, one in each square that avoids $o$; the middle
square (grey) contains $o$. The centres of the six arcs are the markers of
Definition 7.5, at 30°, 90°, …, 330°.*

*Sketch.* At most one square contains the disk centre, so six squares avoid
it. Each of them gets a marker, a direction from the disk centre computed from
where the centre lies relative to the square. In a disk of radius below
$R_7$, two disjoint squares always have markers more than $\frac\pi3$ apart;
six directions cannot all be that far apart. The pair theorem is the heart of
the proof: it places the two squares in a normal position, computes their
shadows on the four edge directions exactly, and shows that the shadows
overlap whenever the markers are at most $\frac\pi3$ apart. At radius $R_7$
the markers can be exactly $\frac\pi3$ apart, but only when neighbouring
squares touch as in (1), which rebuilds the packing up to the position of the
middle column.

Unlike three to five squares, the argument is about pairs of squares rather
than arcs of a single circle, and it uses the disk only through
$\varphi(a_S, b_S) < \frac{13}4$, or $\le \frac{13}4$ for uniqueness.

*Lean:
[`Seven.attainment`](../../SquaresInCircles/Seven/Construction.lean#L126),
[`Seven.sliding_packing`](../../SquaresInCircles/Seven/Construction.lean#L90),
[`Seven.optimality`](../../SquaresInCircles/Seven/Optimality.lean#L38),
[`Seven.uniqueness`](../../SquaresInCircles/Seven/Uniqueness.lean#L22), in
[`SquaresInCircles/Seven/`](../../SquaresInCircles/Seven).*

## Construction

### Proposition 7.1 (the sliding packings)

For $y_1, y_2, y_3$ as in Theorem 7, the squares $Q(\pm1, \pm\frac12)$,
$Q(0, y_1)$, $Q(0, y_2)$, $Q(0, y_3)$ are pairwise disjoint and lie in the
closed disk of radius $R_7$ about the origin. With $(y_1, y_2, y_3) =
(-1, 0, 1)$ they are $Q(c_1), \dots, Q(c_7)$.

*Proof.* Any two of the centres differ by at least 1 in one coordinate. The
side squares lie in $[-\frac32, \frac32] \times [-1, 1]$ and the middle ones in
$[-\frac12, \frac12] \times [-\sqrt3, \sqrt3]$, and

```math
\tfrac94 + 1 = \tfrac14 + 3 = \tfrac{13}4 = R_7^2 .
```

Apply [Lemma 20](common.md#lemma-20-axis-parallel-squares). $\square$

The four outer corners $(\pm\frac32, \pm1)$ lie on the circle. The middle
squares reach it only at the ends of their range, so the column has
$2\sqrt3 - 3$ of slack in total.

*Lean: [`Seven.Column`](../../SquaresInCircles/Seven/Construction.lean#L42),
[`Seven.slidingModel_disjoint`](../../SquaresInCircles/Seven/Construction.lean#L70),
[`Seven.sliding_packing`](../../SquaresInCircles/Seven/Construction.lean#L90),
[`Seven.model_packing`](../../SquaresInCircles/Seven/Construction.lean#L124),
[`Seven.attainment`](../../SquaresInCircles/Seven/Construction.lean#L126).*

## Lower bound

### Proposition 7.2 (lower bound)

If seven pairwise disjoint unit squares lie in the closed disk of radius $R$
about $o$, then $R^2 \ge \frac{13}4$.

The proof takes five steps.

1. **Six exterior squares.** At most one square contains $o$.
2. **States and markers.** A smaller disk gives each exterior square a state
   in a region of the $(a, u)$-plane, and a marker.
3. **The marker arc.** Each exterior square holds a closed arc of the unit
   circle about its marker.
4. **The pair theorem.** Two disjoint exterior squares have markers more than
   $\frac\pi3$ apart.
5. **Conclusion.** Six such markers do not fit on the circle.

*Lean:
[`Seven.squared_lower`](../../SquaresInCircles/Seven/Optimality.lean#L31),
[`Seven.optimality`](../../SquaresInCircles/Seven/Optimality.lean#L38).*

### Step 1. Six exterior squares

#### Lemma 7.3 (six exterior squares)

Among seven pairwise disjoint squares, some six do not contain $o$ in their
interior.

*Proof.* Two disjoint squares cannot both contain $o$
([Definition 7](common.md#definition-7-containing-and-exterior-squares)). Drop
the square that contains $o$, if there is one, and any square otherwise.
$\square$

*Lean:
[`Seven.six_exterior_indices`](../../SquaresInCircles/Seven/ExteriorSelection.lean#L35),
[`Seven.packing_reindex`](../../SquaresInCircles/Seven/ExteriorSelection.lean#L28).*

### Step 2. States and markers

For an exterior square $S$ take a chart $(\theta_S, \varepsilon_S)$
([Lemma 10](common.md#lemma-10-charts)). In it $S$ is the axis-parallel square
centred at $(a_S, b_S)$, with $a_S \ge b_S \ge 0$ and $a_S \ge \frac12$. From
here on only these two numbers and the orientation matter.

#### Definition 7.4 (states)

A *state* is a pair $(a, u)$ with $\frac12 \le a$ and $0 \le u \le a$. It is
*admissible* if $\varphi(a, u) \le \frac{13}4$, and *strictly admissible* if
$\varphi(a, u) < \frac{13}4$. Its *remainder* is

```math
r(a, u) = 4 - 3a - 2u = (a - 1)^2 + \left(u - \tfrac12\right)^2 + \tfrac{13}4 - \varphi(a, u) .
```

By [Lemma 1](common.md#lemma-1-farthest-vertex), in a disk of radius $R$ with
$R^2 < \frac{13}4$ every exterior square has a strictly admissible state
$(a_S, b_S)$. The identity says that $r \ge 0$ is the tangent half-plane of
$\varphi = \frac{13}4$ at $(1, \frac12)$
([Lemma 2](common.md#lemma-2-tangent-lines)); $r > 0$ on strictly admissible
states. In the packing of Theorem 7 the four side squares have the state
$(1, \frac12)$ and the top and bottom squares $(1, 0)$; sliding the column
turns the latter into $(y, 0)$ with $\frac52 - \sqrt3 \le y \le \sqrt3 - \frac12$.

*Lean: [`Seven.Admissible`](../../SquaresInCircles/Seven/Labels.lean#L24),
[`Seven.StrictlyAdmissible`](../../SquaresInCircles/Seven/Labels.lean#L27),
[`Seven.remainder`](../../SquaresInCircles/Seven/Labels.lean#L22),
[`Seven.remainder_identity`](../../SquaresInCircles/Seven/Labels.lean#L33),
[`Seven.chart_strictlyAdmissible`](../../SquaresInCircles/Seven/Labels.lean#L225).*

#### Definition 7.5 (labels and markers)

For a state $(a, u)$ let

```math
\mathrm{axial}(u) = \tfrac54 u, \qquad
\mathrm{side}(a, u) = \tfrac\pi6 + \tfrac13\left(u - \tfrac12\right) + \tfrac34(1 - a), \qquad
\ell(a, u) = \min\left(\mathrm{axial}(u), \mathrm{side}(a, u), \tfrac\pi4\right) .
```

$\ell$ is the *label*; it is *axial*, *side* or *capped* according to which
term attains the minimum, and *active* unless it is capped. The *marker* of an
exterior square $S$ is the direction $\theta_S + \varepsilon_S\,\ell(a_S, b_S)$.

The label is an angle measured in the chart from the phase, towards the
centre of $S$. In the optimal packing the side squares have
$\ell = \mathrm{side}(1, \frac12) = \frac\pi6$ and the top and bottom
squares $\ell = \mathrm{axial}(0) = 0$, which puts the six markers at
30°, 90°, …, 330°, exactly $\frac\pi3$ apart (figure above). The axial and side
labels agree on the line $9a + 11u = 2\pi + 7$, which meets the circle
$\varphi = \frac{13}4$ at the *transition state*
$(a_0, u_0) \approx (1.1198, 0.2914)$, of label $s_0 = \frac54 u_0 \approx 0.364$.

*Lean: [`Seven.axial`](../../SquaresInCircles/Seven/Labels.lean#L19),
[`Seven.side`](../../SquaresInCircles/Seven/Labels.lean#L20),
[`Seven.label`](../../SquaresInCircles/Seven/Labels.lean#L21),
[`Seven.chartMarker`](../../SquaresInCircles/Seven/Labels.lean#L217),
[`Seven.Boundary.a0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L19),
[`Seven.Boundary.u0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L20),
[`Seven.Boundary.s0`](../../SquaresInCircles/Seven/LabelBoundary.lean#L21).*

#### Lemma 7.6 (the label)

Let $(a, u)$ be admissible. Then $3a + 2u \le 4$, $a < \frac54$,
$u < \frac{31}{40}$ and $0 \le \ell(a, u) \le \frac\pi4$, with $\ell = 0$ only
if $u = 0$. Moreover

```math
\mathrm{side}(a, u) = \tfrac\pi6 + \tfrac56\left(u - \tfrac12\right) + \tfrac14 r(a, u)
= \tfrac\pi6 - \tfrac54(a - 1) - \tfrac16 r(a, u) .
```

*Proof.* The first inequality is $r \ge 0$, and the two bounds follow from
$\varphi(a, u) \le \frac{13}4$ with $u \ge 0$ and $u \le a$. The label is a
minimum of three nonnegative terms, one of which is $\frac\pi4$, and
$\mathrm{axial}(u) = 0$ only at $u = 0$, while the side label is
positive. The identities are the definition of $r$. $\square$

*Lean:
[`Seven.Admissible.tangent`](../../SquaresInCircles/Seven/Labels.lean#L59),
[`Seven.Admissible.a_lt_five_fourths`](../../SquaresInCircles/Seven/Labels.lean#L64),
[`Seven.Admissible.u_lt`](../../SquaresInCircles/Seven/Labels.lean#L81),
[`Seven.Admissible.label_nonneg`](../../SquaresInCircles/Seven/Labels.lean#L89),
[`Seven.Admissible.label_le_quarter`](../../SquaresInCircles/Seven/Labels.lean#L104),
[`Seven.Admissible.label_zero_iff`](../../SquaresInCircles/Seven/Labels.lean#L110),
[`Seven.side_identity_transverse`](../../SquaresInCircles/Seven/Labels.lean#L38),
[`Seven.side_identity_radial`](../../SquaresInCircles/Seven/Labels.lean#L43).*

### Step 3. The marker arc

#### Lemma 7.7 (the marker arc)

Let $(a, u)$ be admissible and $|t - \ell(a, u)| \le \frac{801}{1600}$. Then

```math
|\cos t - a| \le \tfrac12 , \qquad |\sin t - u| \le \tfrac12 .
```

So an exterior square $S$ with an admissible state holds, in its closed
square, the arc of the unit circle $\Gamma_1$ of half-width
$\frac{801}{1600} \approx 28.7°$ about its marker. At the optimal packing the
arcs of the figure have half-width exactly $\frac\pi6 \approx 30°$.

*Proof.* In the chart, the point $(\cos t, \sin t)$ must stay between the
four edge lines of $Q(a, u)$.

- *The far edge* $x = a + \frac12$ is out of reach, since $a \ge \frac12$.
- *The near edge* $x = a - \frac12$: we need
  $\ell + \frac{801}{1600} < \arccos(a - \frac12)$. By the radial form of the
  side label and $\varphi \le \frac{13}4$, $\ell + \arcsin(a - \frac12)$ is at
  most an explicit function of $x = a - \frac12 \in [0, \frac34]$,

  ```math
  \tfrac\pi6 + \tfrac1{24} + \tfrac13\sqrt{\tfrac{13}4 - (x + 1)^2} + \arcsin x - \tfrac34 x .
  ```

  This envelope is concave (its second derivative has the sign of an explicit
  polynomial with positive Bernstein coefficients) and decreasing from
  $x = \frac14$ on, and a Cauchy–Schwarz bound on $[0, \frac14]$ gives the
  maximum $\frac\pi6 + \frac{\sqrt{87061} - 86}{384} < \frac\pi2 - \frac{801}{1600}$.
- *The lower edge* $y = u - \frac12$: we need
  $\arcsin(u - \frac12) + \frac{801}{1600} < \ell$. Each of the three terms of
  $\ell$ exceeds the left side: the axial one because
  $\frac54 u - \arcsin(u - \frac12)$ increases from $\frac\pi6$, the side one by
  $\arcsin y \le y + \frac{y^3}4$ and a Cauchy–Schwarz bound on
  $\frac34(a + \frac12) + \frac23(u + \frac12)$, and $\frac\pi4$ because
  $u < \frac{31}{40}$.
- *The upper edge* $y = u + \frac12$ matters only when $u \le \frac12$, and
  then $\ell + \frac{801}{1600} < \arcsin(u + \frac12)$ follows from
  $\ell \le \frac54 u$ and the tangent of $\arcsin$ at $\frac35$. $\square$

*Lean: [`Seven.marker_arc`](../../SquaresInCircles/Seven/MarkerArc.lean#L153),
[`Seven.marker_lower_endpoint`](../../SquaresInCircles/Seven/MarkerArc.lean#L46),
[`Seven.marker_vertical_endpoint`](../../SquaresInCircles/Seven/MarkerArc.lean#L69),
[`Seven.marker_horizontal_endpoint`](../../SquaresInCircles/Seven/MarkerArc.lean#L135),
[`Seven.arcEnvelope_bound`](../../SquaresInCircles/Seven/ArcAnalysis.lean#L262),
[`Seven.arcCurvaturePolynomial_pos`](../../SquaresInCircles/Seven/ArcAnalysis.lean#L71).*

### Step 4. The pair theorem

The rest of the proof compares two exterior squares with states $(a, u)$ and
$(A, v)$ and orientations $s, t \in \lbrace 1, -1 \rbrace$. Put the first in
its chart; the second is then turned relative to it by the angle between the
two phases.

#### Definition 7.8 (support function)

For a point $(a, b)$ and a direction $z$ let

```math
h(a, b, z) = a\cos z + b\sin z + \tfrac12\left(|\cos z| + |\sin z|\right)
= \max_{p \in \overline{Q(a, b)}} \langle p,\ u(z)\rangle ,
```

the support function of the axis-parallel unit square centred at $(a, b)$.

*Lean: [`Seven.support`](../../SquaresInCircles/Seven/Support.lean#L8),
[`Seven.point_le_support`](../../SquaresInCircles/Seven/Support.lean#L68).*

#### Definition 7.9 (canonical pair and support sums)

Given two states $(a, u)$, $(A, v)$, signs $s, t$ and a gap $g \ge 0$, let

```math
d = g + s\,\ell(a, u) - t\,\ell(A, v) .
```

The *canonical pair* is $S = Q(a, su)$ and the unit square $T$ whose frame is
turned by $d$ and which sits at $(A, tv)$ in that frame. The markers of $S$
and $T$ are the directions $s\ell(a, u)$ and $d + t\ell(A, v)$: they are $g$
apart. For $k = 0, 1, 2, 3$ the *support sum* on the $k$-th axis is

```math
\sigma_k(g) = h\left(a, su, k\tfrac\pi2\right) + h\left(A, tv, k\tfrac\pi2 + \pi - d\right)
= \max_{\overline S}\,\langle \cdot, n_k\rangle - \min_{\overline T}\,\langle \cdot, n_k\rangle ,
```

where $n_k = u(k\frac\pi2)$ is the outer normal of the $k$-th edge of $S$. In
the chart of $S$, whose disk centre is the origin, $n_0$ points away from the
centre and $n_2$ towards it, $n_1$ points in the direction of increasing angle,
towards the marker of $T$, and $n_3$ the other way.

*Lean: [`Seven.pairSupport`](../../SquaresInCircles/Seven/PairModel.lean#L19),
[`Seven.relativePhase`](../../SquaresInCircles/Seven/CanonicalPair.lean#L25),
[`Seven.pair_support_axis_values`](../../SquaresInCircles/Seven/CanonicalPair.lean#L36).*

#### Lemma 7.10 (separating axes)

If $\sigma_k(g) > 0$ for every $k$, both for a canonical pair and for the pair
seen from $T$, then the open squares $S^\circ$ and $T^\circ$ meet.

*Proof.* $\sigma_k > 0$ and $\sigma_{k+2} > 0$ say that the open shadows of $S$
and $T$ on the line of $n_k$ overlap, so the shadows overlap on both axes of
$S$. Reversing the pair and reflecting it, which exchanges the two squares and
both signs but keeps $d$, gives the same for the two axes of $T$. If $S$ and
$T$ were disjoint, [Lemma 5](common.md#lemma-5-supporting-line) would give a
normal $n$ with $w_S(n) + w_T(n) \le \langle n, c_T - c_S\rangle$. Writing
$c_T - c_S$ in the frame of $S$, the four strict overlaps bound
$\langle n, c_T - c_S\rangle$ strictly by the octagon
$\frac12(|n_1| + |n_2| + |c\,n_1 + s\,n_2| + |{-s}\,n_1 + c\,n_2|) = w_S(n) + w_T(n)$,
where $(c, s)$ is the relative frame: a weighted sum of two of the four
overlaps, with the weights read off the quadrant of $n$. This is the
separating-axis theorem for two squares. $\square$

*Lean:
[`Seven.SAT.separating_axes`](../../SquaresInCircles/Seven/SeparatingAxes.lean#L271),
[`Seven.SAT.all_normals_strict`](../../SquaresInCircles/Seven/SeparatingAxes.lean#L231),
[`Seven.all_four_axes_inside`](../../SquaresInCircles/Seven/CanonicalPair.lean#L106),
[`Seven.canonical_pair_overlap`](../../SquaresInCircles/Seven/CanonicalPair.lean#L157).*

#### Proposition 7.11 (the gap of $\frac\pi3$)

Let $(a, u)$ and $(A, v)$ be admissible. Then $\sigma_k(\frac\pi3) \ge 0$ for
every $k$ and all signs, and $\sigma_k(\frac\pi3) > 0$ if both states are
strictly admissible.

*Proof.* First the capped labels. On the triangle where $\ell = \frac\pi4$,
cut out by $\pi \le 5u$ and $9a - 4u \le 7 - \pi$, the label is constant, so
$\sigma_k$ is affine in the state. Its three vertices
$(\frac\pi5, \frac\pi5)$, $(\frac{7 - \pi/5}9, \frac\pi5)$ and
$(\frac{7 - \pi}5, \frac{7 - \pi}5)$ are strictly admissible and have active
labels (axial or side equal to $\frac\pi4$). So $\sigma_k$ at a capped state
is a convex combination of values at active states, and both conclusions pass
over. It remains to treat active labels, sector by sector:

| axis | signs $(s, t)$ | labels | argument |
| --- | --- | --- | --- |
| $n_0$, outward | all | all | $\sigma_0 = a + \frac12 + h_T \ge 1 + (1 - \sqrt3)$, since $T$'s centre is within $\sqrt3 - \frac12$ of the origin |
| $n_3$, backward | all | all | $T$ contains its marker point, which reaches past $S$ |
| $n_2$, inward | $(-, \pm)$ | all | $T$'s marker arc (Lemma 7.7) reaches past $S$ |
| $n_2$, inward | $(+, +)$ | both axial | one universal trigonometric profile, positive on $(0, \frac\pi2]$ |
| $n_2$, inward | $(+, +)$ | side, axial | scalar bounds on the relative turn; $\sigma_2 = 0$ only at the contact of a side square and the top square of the optimal packing |
| $n_2$, inward | $(+, +)$ | any, side | concave in the first label; the endpoints $0$ and $\frac\pi4$ |
| $n_2$, inward | $(+, -)$ | active | exact formula; minima on the boundary curves of the label regions; a two-circle quadratic certificate |
| $n_1$, forward | $(+, +)$ | all | marker bounds and $\cos + \sin$ on $[0, \frac\pi4]$ |
| $n_1$, forward | $(+, -)$, and $(-, -)$ with $S$ axial | active | profiles of the target support along the label boundaries |
| $n_1$, forward | $(-, +)$ | active | a Cauchy–Schwarz certificate for two side labels, with $\sigma_1 = 0$ only at the contact of two side squares; linear clearances for the others |
| $n_1$, forward | $(-, -)$, $S$ side | active | the target support is minimised along exact label segments; its circular piece is concave |

In each sector $\sigma_k$ is written in closed form, reduced by monotonicity
or concavity to the boundary of the label region, and bounded below by a
function of one angle. That function is compared with Taylor polynomials of
$\sin$ and $\cos$ of degree up to 11, and the resulting polynomial is shown
positive by its coefficients in a Bernstein basis, by an exact
sum-of-squares identity, or at a single point together with a curvature
bound. All constants are rational or radicals in $\pi$, and $\pi$ enters
through $3.141592 < \pi < 3.141593$. Strictness is carried from the original
states throughout, never assumed for a boundary point chosen during a
minimisation. $\square$

At radius $R_7$, $\sigma_k(\frac\pi3)$ vanishes only where two squares touch
as in the optimal packing: the two squares of a side column, or a side square
and the top or bottom square (Proposition 7.18). In the second case the
equality fixes the side state $(1, \frac12)$ and puts the other square on the
axis, $v = 0$, but leaves its height $A$ free, as the sliding column
requires.

*Lean: [`Seven.fixed_gap_pos`](../../SquaresInCircles/Seven/FixedGap.lean#L60),
[`Seven.fixed_gap_nonneg`](../../SquaresInCircles/Seven/FixedGap.lean#L54),
[`Seven.fixed_gap_property`](../../SquaresInCircles/Seven/FixedGap.lean#L49),
[`Seven.fixed_gap_of_active_cases`](../../SquaresInCircles/Seven/CapReduction.lean#L206),
[`Seven.fixed_gap_active`](../../SquaresInCircles/Seven/FixedGap.lean#L23),
[`Seven.fixed_gap_outward`](../../SquaresInCircles/Seven/EasySectors.lean#L40),
[`Seven.fixed_gap_backward`](../../SquaresInCircles/Seven/EasySectors.lean#L47),
[`Seven.fixed_gap_inward_negative`](../../SquaresInCircles/Seven/EasySectors.lean#L82),
[`Seven.inward_axial_axial_pos`](../../SquaresInCircles/Seven/InwardAxialAxial.lean#L71),
[`Seven.inward_side_axial_pos`](../../SquaresInCircles/Seven/InwardSideAxial.lean#L110),
[`Seven.inward_side_axial_eq_zero`](../../SquaresInCircles/Seven/InwardSideAxial.lean#L119),
[`Seven.fixed_gap_inward_side_target`](../../SquaresInCircles/Seven/InwardSideTarget.lean#L236),
[`Seven.fixed_gap_inward_opposite_active`](../../SquaresInCircles/Seven/InwardOpposite.lean#L213),
[`Seven.fixed_gap_forward_positive`](../../SquaresInCircles/Seven/ForwardPositive.lean#L32),
[`Seven.fixed_gap_forward_negative_target`](../../SquaresInCircles/Seven/ForwardNegativeTarget.lean#L257),
[`Seven.fixed_gap_forward_opposite_active`](../../SquaresInCircles/Seven/OppositeForward.lean#L309),
[`Seven.sideSide_support_pos`](../../SquaresInCircles/Seven/SideSide.lean#L175),
[`Seven.fixed_gap_forward_both_negative_side`](../../SquaresInCircles/Seven/ForwardBothNegative.lean#L395).*

#### Lemma 7.12 (small gaps)

Let $(a, u)$ and $(A, v)$ be admissible and $0 \le g \le 1$. Then
$\sigma_k(g) > 0$ for every $k$ and all signs.

*Proof.* By Lemma 7.7 the closed squares $\overline S$ and $\overline T$ hold
the arcs of $\Gamma_1$ of half-width $\frac{801}{1600}$ about their markers,
which are $g \le 1$ apart. Both arcs therefore contain the three points of
$\Gamma_1$ in the directions $m$ and $m \pm \frac1{3200}$, where $m$ is the
midpoint of the markers. If $\sigma_k(g) \le 0$, the line of $n_k$ through the
top of $\overline S$ would separate the two closed squares weakly, and all
three points would lie on it. A line meets a circle in at most two points.
$\square$

*Lean:
[`Seven.small_gap_support_pos`](../../SquaresInCircles/Seven/SmallAndParallelGaps.lean#L15),
[`Seven.marker_arc_support`](../../SquaresInCircles/Seven/EasySectors.lean#L32).*

#### Lemma 7.13 (the minimum of a support sum)

Let $(a, u)$ and $(A, v)$ be strictly admissible and suppose $\sigma_k$ is
positive at $1$ and at $\frac\pi3$ but not on all of $[1, \frac\pi3]$. Let $g$
be the leftmost point of $[1, \frac\pi3]$ where $\sigma_k$ attains its minimum.
Then $\sigma_k(g) > 0$, a contradiction.

*Proof.* Only the second term of $\sigma_k$ depends on $g$, through the
direction $z = k\frac\pi2 + \pi - d$.

- *A cardinal direction.* If $\sin z = 0$ or $\cos z = 0$, then $d = 0$ or
  $d = \frac\pi2$: the two squares are parallel. Then $\sigma_k$ is 1 plus or
  minus a difference of centre coordinates, and it can fail to be positive
  only if the squares lie side by side across the axis. That is excluded by
  the labels. For strictly admissible states, two labels on opposite sides
  with $u + v \ge 1$ add up to more than $\frac\pi3$, and $d = 0$ would make
  $g$ equal to their sum. When $d = \frac\pi2$, a separation by a whole side
  forces $s\ell(a, u) - t\ell(A, v) < \frac\pi6$, and then
  $g = \frac\pi2 - s\ell(a, u) + t\ell(A, v) > \frac\pi3$.
- *A smooth minimum.* Otherwise $h(A, tv, z)$ is a sinusoid
  $X\cos z + Y\sin z$ near $g$, where $(X, Y)$ is a vertex of $T$. By
  Fermat's theorem its derivative vanishes, and a comparison with a point to
  the left, where $\sigma_k$ is strictly larger, shows that
  $X\cos z + Y\sin z < 0$. So $u(z)$ points away from the vertex of $T$
  nearest to the origin, at distance $\delta = |(X, Y)| < \frac12$, and the
  term equals $-\delta$. The first term, the support of $S$, exceeds
  $\delta$: on the axes where it could be small, the side label of $T$ and
  the axial label of $S$ bound the angles, and elementary estimates for
  $\sin$ and $\cos$ finish. $\square$

The leftmost choice matters when $\sigma_k$ is constant on a stretch: then no
point of the stretch but its left end is a leftmost minimum.

*Lean:
[`Seven.leftmost_nonpositive_minimum`](../../SquaresInCircles/Seven/AngularMinima.lean#L67),
[`Seven.sinusoid_leftmost_minimum`](../../SquaresInCircles/Seven/AngularMinima.lean#L106),
[`Seven.cardinal_target_support_pos`](../../SquaresInCircles/Seven/SmallAndParallelGaps.lean#L171),
[`Seven.opposite_transverse_labels_gt`](../../SquaresInCircles/Seven/ParallelLabels.lean#L57),
[`Seven.quarter_difference_gt`](../../SquaresInCircles/Seven/ParallelLabels.lean#L139),
[`Seven.stationary_nearest_corner`](../../SquaresInCircles/Seven/NearestCornerMinimum.lean#L65),
[`Seven.corner_source_margin`](../../SquaresInCircles/Seven/NearestCornerMinimum.lean#L148),
[`Seven.smooth_leftmost_support_pos`](../../SquaresInCircles/Seven/NearestCornerMinimum.lean#L249).*

#### Theorem 7.14 (all gaps)

Let $(a, u)$ and $(A, v)$ be strictly admissible and $0 \le g \le \frac\pi3$.
Then $\sigma_k(g) > 0$ for every $k$ and all signs; hence the open squares of
the canonical pair meet.

*Proof.* Lemma 7.12 covers $g \le 1$. For $g > 1$, if $\sigma_k(g) \le 0$,
then $\sigma_k(1) > 0$ (Lemma 7.12), $\sigma_k(\frac\pi3) > 0$
(Proposition 7.11), and Lemma 7.13 gives a contradiction. The pair seen from
$T$ is again a canonical pair of strictly admissible states, so Lemma 7.10
applies. $\square$

*Lean:
[`Seven.all_gap_support_pos`](../../SquaresInCircles/Seven/AllGaps.lean#L22),
[`Seven.canonical_pair_overlap`](../../SquaresInCircles/Seven/CanonicalPair.lean#L157).*

#### Theorem 7.15 (marker separation)

Let $S$ and $T$ be disjoint exterior squares with
$\varphi(a_S, b_S) < \frac{13}4$ and $\varphi(a_T, b_T) < \frac{13}4$. Then
their markers are more than $\frac\pi3$ apart.

*Proof.* Suppose not. Swapping $S$ and $T$ if needed, the marker of $T$ is
$g \in [0, \frac\pi3]$ ahead of that of $S$. Let $s = \varepsilon_S$ and
$t = \varepsilon_T$. By [Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart),
$S$ sits at $(a_S, s\,b_S)$ in the frame $\theta_S$ and $T$ at $(a_T, t\,b_T)$ in
the frame $\theta_T$, and $\theta_T - \theta_S = d$ because the markers are
$g$ apart. So, read in the frame $\theta_S$, the two squares are the canonical
pair of their states, and Theorem 7.14 gives a common interior point.
$\square$

*Lean:
[`Seven.marker_separation`](../../SquaresInCircles/Seven/MarkerSeparation.lean#L66),
[`Seven.close_ordered_charts_overlap`](../../SquaresInCircles/Seven/MarkerSeparation.lean#L34),
[`Seven.chartMarker_formula`](../../SquaresInCircles/Seven/MarkerSeparation.lean#L27).*

### Step 5. Conclusion

#### Lemma 7.16 (six markers)

Six directions cannot be pairwise more than $\frac\pi3$ apart.

*Proof.* Otherwise closed arcs of a common half-width $r > \frac\pi6$ about
them are pairwise disjoint, and their total length $12r$ exceeds $2\pi$
([Lemma 7](common.md#lemma-7-angular-budget)). $\square$

*Lean:
[`Seven.six_markers_impossible`](../../SquaresInCircles/Seven/CircleBudget.lean#L37),
[`closed_arc_budget`](../../SquaresInCircles/Common/AngularBudget.lean#L49).*

*Proof of Proposition 7.2.* Suppose $R^2 < \frac{13}4$. By Lemma 7.3 six of the
squares are exterior, and by Lemma 1 each has a strictly admissible state.
By Theorem 7.15 their markers are pairwise more than $\frac\pi3$ apart, which
Lemma 7.16 excludes. $\square$

## Uniqueness

*Idea.* Run the lower bound again at radius exactly $R_7$. The support sums may
now vanish, but only at the gap $\frac\pi3$, and only where two squares touch
as they do in the packings of Theorem 7. So some square contains $o$, the
markers of the other six form a regular hexagon, and going round it each
square touches the next in a fixed pattern. That pattern rebuilds the two side
columns and puts one square above $o$ and one below, each at a free height.
The side columns then pin the square that contains $o$ to the middle column,
where it can slide too.

### Definition 7.17 (contacts)

A state is a *side state* if it is $(1, \frac12)$, and an *axial state* if it
is $(a, 0)$ with $\frac12 \le a \le \sqrt3 - \frac12$. States $(a, u)$ and
$(A, v)$ with signs $s$ and $t$ form a *contact* if

1. $s = -1$, $t = +1$, and both states are side states; or
2. $s = +1$, $(a, u)$ is a side state and $(A, v)$ is axial; or
3. $t = -1$, $(a, u)$ is axial and $(A, v)$ is a side state.

Going counterclockwise round a packing of Theorem 7, these are the three ways
in which an exterior square touches the next one: (1) the first square of a
side column touches the second, (2) a side column touches the top or bottom
square, and (3) the top or bottom square touches the next side column. The
label of a side state is $\frac\pi6$ and that of an axial state is $0$, so no
state in a contact has a capped label.

*Lean:
[`Seven.Equality.OrderedContact`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L19),
[`Seven.Equality.Side`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L16),
[`Seven.Equality.Axial`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L17),
[`Seven.Equality.contact_label_not_cap`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L48).*

### Proposition 7.18 (zeros at the gap of $\frac\pi3$)

Let $(a, u)$ and $(A, v)$ be admissible. If $\sigma_k(\frac\pi3) = 0$ for some
$k$ and signs $s$, $t$, then the two states with these signs form a contact.

*Proof.* Go through the sectors of Proposition 7.11 again, first with active
labels. In most of them the lower bound is positive for all admissible states.
The others are forward with signs $(+, -)$, $(-, +)$ or $(-, -)$, and inward
with signs $(+, +)$ or $(+, -)$. There the bound is tight only when the turn
between the two labels and one of the remainders $r$ vanish. By the identity
of Definition 7.4, $r(a, u) = 0$ with $\varphi(a, u) \le \frac{13}4$ forces
$(a, u) = (1, \frac12)$. The turn then fixes the other label, which makes the
other state a side state or gives it transverse coordinate 0, and an
admissible state $(A, 0)$ is axial, since $\varphi(A, 0) \le \frac{13}4$ gives
$A \le \sqrt3 - \frac12$. A capped label reduces to active ones as in
Proposition 7.11: $\sigma_k$ at a capped state is a convex combination of its
values at the three vertices of the triangle, which are nonnegative, so it
vanishes at a vertex of positive weight. That vertex would be in a contact,
but its label is $\frac\pi4$. $\square$

*Lean:
[`Seven.Equality.fixed_gap_zero`](../../SquaresInCircles/Seven/Uniqueness/FixedGapEquality.lean#L85),
[`Seven.Equality.fixed_gap_zero_active`](../../SquaresInCircles/Seven/Uniqueness/FixedGapEquality.lean#L13),
[`Seven.Equality.remainder_zero`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L24),
[`Seven.Equality.axial_of_transverse_zero`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L31),
[`Seven.Equality.side_side_zero`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L74),
[`Seven.Equality.inward_opposite_zero`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L119),
[`Seven.Equality.forward_negative_target_zero`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L174),
[`Seven.inward_side_axial_eq_zero`](../../SquaresInCircles/Seven/InwardSideAxial.lean#L119).*

### Lemma 7.19 (closed containment)

Let $(a, u)$ and $(A, v)$ be admissible. Then $\sigma_k(g) \ge 0$ for
$0 \le g \le \frac\pi3$, and $\sigma_k(g) > 0$ for $0 \le g < \frac\pi3$.

*Proof.* For $0 < e \le 1$ the states $((1 - e)a + \frac e2, (1 - e)u)$ are
strictly admissible, by the identity

```math
\tfrac{13}4 - \varphi\left((1 - e)a + \tfrac e2,\ (1 - e)u\right)
= (1 - e)\left(\tfrac{13}4 - \varphi(a, u)\right) + 2e
+ e(1 - e)\left(\left(a - \tfrac12\right)^2 + u^2\right),
```

and they tend to $(a, u)$ as $e \to 0$. Theorem 7.14 applies to them, and
$\sigma_k(g)$ is continuous in the states, so $\sigma_k(g) \ge 0$.

For the strict inequality, Lemma 7.12 covers $g \le 1$. Suppose
$\sigma_k(g) = 0$ with $1 < g < \frac\pi3$, and let $x$ be the least zero of
$\sigma_k$ in $[1, g]$. Since $\sigma_k \ge 0$ on $[1, \frac\pi3]$, $x$ is the
leftmost point where $\sigma_k$ attains its minimum there, and $x > 1$. The two
cases of Lemma 7.13 still give $\sigma_k(x) > 0$. The smooth case needs only
admissible states. In the cardinal case the label bounds hold with $\ge$ and
$\le$ in place of $>$ and $<$, which gives $x \ge \frac\pi3$ instead of
$x > \frac\pi3$, still a contradiction. $\square$

*Lean:
[`Seven.Equality.all_gap_nonneg`](../../SquaresInCircles/Seven/Uniqueness/ClosedGaps.lean#L47),
[`Seven.Equality.all_gap_pos_below`](../../SquaresInCircles/Seven/Uniqueness/ClosedGaps.lean#L67),
[`Seven.Equality.cardinal_target_pos_below`](../../SquaresInCircles/Seven/Uniqueness/ClosedParallel.lean#L141),
[`Seven.Equality.opposite_labels_ge`](../../SquaresInCircles/Seven/Uniqueness/ClosedParallel.lean#L13).*

### Proposition 7.20 (closed marker separation)

Let $S$ and $T$ be disjoint exterior squares with
$\varphi(a_S, b_S) \le \frac{13}4$ and $\varphi(a_T, b_T) \le \frac{13}4$.
Then their markers are at least $\frac\pi3$ apart. If the marker of $T$ is
exactly $\frac\pi3$ ahead of that of $S$, their states and signs
$\varepsilon_S$, $\varepsilon_T$ form a contact.

*Proof.* As in Theorem 7.15, if the marker of $T$ is $g \in [0, \frac\pi3]$
ahead of that of $S$, the two squares are the canonical pair of their states.
They are disjoint, so by Lemma 7.10 some support sum is at most 0, for the
pair or for the pair seen from $T$. For $g < \frac\pi3$ this contradicts
Lemma 7.19. For $g = \frac\pi3$ that sum is 0 by Lemma 7.19, and
Proposition 7.18 gives a contact. Seen from $T$, the contact is one of the
reversed pair with both signs flipped, which is a contact of the pair itself.
$\square$

*Lean:
[`Seven.Equality.marker_separation_closed`](../../SquaresInCircles/Seven/Uniqueness/PairGeometry.lean#L151),
[`Seven.Equality.ordered_chart_contact`](../../SquaresInCircles/Seven/Uniqueness/PairGeometry.lean#L176),
[`Seven.Equality.canonical_has_separator`](../../SquaresInCircles/Seven/Uniqueness/PairGeometry.lean#L58),
[`Seven.Equality.reflected_reverse_contact`](../../SquaresInCircles/Seven/Uniqueness/ScalarEquality.lean#L59).*

### Lemma 7.21 (the hexagon)

1. Six directions pairwise at least $\frac\pi3$ apart are, in some order,
   $\phi + i\frac\pi3$ for $i = 0, \dots, 5$.
2. Seven directions cannot be pairwise at least $\frac\pi3$ apart.
3. In a packing of seven unit squares in a closed disk of radius $R_7$ about
   $o$, some square contains $o$.

*Proof.* (1) Sort the directions round the circle. The six gaps between
neighbours, including the one that wraps round, are at least $\frac\pi3$ and
add up to $2\pi$, so each is exactly $\frac\pi3$. (2) The closed arcs of
half-width $\frac12$ about them would be pairwise disjoint, since
$\frac\pi3 > 1$, and have total length $7 > 2\pi$
([Lemma 7](common.md#lemma-7-angular-budget)). (3) Otherwise all seven squares
are exterior, with admissible states by
[Lemma 1](common.md#lemma-1-farthest-vertex), and Proposition 7.20 puts their
markers pairwise at least $\frac\pi3$ apart, against (2). $\square$

*Lean:
[`Seven.Equality.six_directions_hexagon`](../../SquaresInCircles/Seven/Uniqueness/Hexagon.lean#L27),
[`Seven.Equality.seven_directions_impossible`](../../SquaresInCircles/Seven/Uniqueness/Hexagon.lean#L102),
[`Seven.Equality.exists_containing`](../../SquaresInCircles/Seven/Uniqueness/Hexagon.lean#L122).*

### Proposition 7.22 (the ring)

Let six pairwise disjoint exterior squares have admissible states. Then in
some frame at $o$ they sit, in some order, at

```math
(1, -\tfrac12),\quad (1, \tfrac12),\quad (0, h),\quad (-1, \tfrac12),\quad (-1, -\tfrac12),\quad (0, -k)
```

for some $h$ and $k$ with $\frac12 \le h, k \le \sqrt3 - \frac12$.

*Proof.* By Proposition 7.20 and Lemma 7.21 the markers form a regular
hexagon, and each square and the next one counterclockwise form a contact.
Call a square with a side state *lower* if its sign is $-1$ and *upper* if it
is $+1$. By Definition 7.17, after a lower square comes an upper one, after an
upper one an axial one, and after an axial one a lower one. So round the
hexagon the kinds are lower, upper, axial, lower, upper, axial. The labels are
$\frac\pi6$ and $0$, so the markers fix the phases: they are $\theta$,
$\theta$, $\theta + \frac\pi2$, $\theta + \pi$, $\theta + \pi$,
$\theta + \frac{3\pi}2$ for the phase $\theta$ of the first lower square. By
[Lemma 11](common.md#lemma-11-cartesian-form-of-a-chart) each square sits, in
the frame of its own phase, at $(1, -\frac12)$ if lower, at $(1, \frac12)$ if
upper, and at $(a, 0)$ if axial. Turning back to the frame $\theta$ by
[Lemma 21](common.md#lemma-21-sitting-at-a-centre) (2) gives the six points;
$h$ and $k$ are the first coordinates of the two axial states. $\square$

*Lean:
[`Seven.Equality.six_exterior_ring`](../../SquaresInCircles/Seven/Uniqueness/ContactCycle.lean#L216),
[`Seven.Equality.ring_of_ordered_contacts`](../../SquaresInCircles/Seven/Uniqueness/ContactCycle.lean#L141),
[`Seven.Equality.contact_kinds`](../../SquaresInCircles/Seven/Uniqueness/ContactCycle.lean#L26),
[`Seven.Equality.hexagon_successor`](../../SquaresInCircles/Seven/Uniqueness/Hexagon.lean#L81),
[`Seven.ExteriorRing`](../../SquaresInCircles/Seven/Uniqueness/ContactCycle.lean#L130).*

### Lemma 7.23 (the square in the middle)

Let $S$ contain $o$, and let four squares disjoint from $S$ sit at
$(\pm1, \pm\frac12)$ in a frame $\phi$ at $o$. Then $S$ sits at $(0, z)$ in the
frame $\phi$, with $|z| < \frac12$.

*Proof.* Work in the frame $\phi$. Every point $(x, y)$ of $S^\circ$ with
$|y| < 1$ has $|x| \le \frac12$. Otherwise some point of the segment from $o$
to $(x, y)$, which lies in $S^\circ$, would have $\frac12 < |x'| \le \frac34$
and $|y'| < 1$, and so lie in one of the closed side squares, against
[Lemma 5](common.md#lemma-5-supporting-line) (2). The centre of $S$ is within
$\frac1{\sqrt2}$ of $o$, so the line through it parallel to the first axis
lies in the band $|y| < 1$. If $S$ were tilted, the chord of $S^\circ$ along
that line would be longer than 1, which does not fit in $|x| \le \frac12$. So
the sides of $S$ are parallel to the axes, its centre is on $x = 0$, and
$|z| < \frac12$ because $S$ contains $o$. $\square$

*Lean:
[`Seven.Equality.central_square_represents`](../../SquaresInCircles/Seven/Uniqueness/CentralSquare.lean#L152),
[`Seven.Equality.central_strip`](../../SquaresInCircles/Seven/Uniqueness/CentralSquare.lean#L61),
[`Seven.Equality.section_strip_rigidity`](../../SquaresInCircles/Seven/Uniqueness/CenterSection.lean#L76).*

### Proposition 7.24 (uniqueness)

If seven pairwise disjoint unit squares lie in the closed disk of radius $R_7$
about $o$, the packing has the normal form of $(\pm1, \pm\frac12)$,
$(0, y_1)$, $(0, y_2)$, $(0, y_3)$ for some $y_1, y_2, y_3$ as in Theorem 7.
Conversely, every such normal form is a packing in that disk.

*Proof.* By Lemma 7.21 some square contains $o$. The other six are exterior,
with admissible states by Lemma 1, and Proposition 7.22 places them in a frame
$\phi$; Lemma 7.23 places the seventh at $(0, z)$ in the same frame. The
squares at $(0, -k)$, $(0, z)$ and $(0, h)$ are disjoint and sit on one axis
of the frame, so $-k + 1 \le z$ and $z + 1 \le h$. With
$h, k \le \sqrt3 - \frac12$ these are the conditions of Theorem 7 for
$(y_1, y_2, y_3) = (-k, z, h)$, and
[Lemma 22](common.md#lemma-22-from-slots-to-a-normal-form) gives the normal
form. The converse is Proposition 7.1, moved to $o$ by the rotation. $\square$

*Lean: [`Seven.uniqueness`](../../SquaresInCircles/Seven/Uniqueness.lean#L22),
[`Seven.packing_iff_sliding`](../../SquaresInCircles/Seven/Uniqueness.lean#L32),
[`Seven.Equality.classify`](../../SquaresInCircles/Seven/Uniqueness/Reconstruction.lean#L134),
[`Seven.Equality.normal_form_of_containing`](../../SquaresInCircles/Seven/Uniqueness/Reconstruction.lean#L74),
[`Seven.Equality.column_centers_separated`](../../SquaresInCircles/Seven/Uniqueness/Reconstruction.lean#L41),
[`Seven.SlidingNormalForm`](../../SquaresInCircles/Seven/Uniqueness/NormalForm.lean#L17),
[`Seven.SlidingNormalForm.packing`](../../SquaresInCircles/Seven/Uniqueness/NormalForm.lean#L45),
[`Seven.classification_by_slots`](../../SquaresInCircles/Seven/Uniqueness.lean#L38).*