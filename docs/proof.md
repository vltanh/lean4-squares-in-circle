# Proof outline

[Back to the README](../README.md)

## One and two squares

- **One square** (`One/`). Write `a = |localX S o|`, `b = |localY S o|` for
  the disk centre `o` in the square's frame. The farthest vertex is at squared
  distance `phi a b = (a + 1/2)² + (b + 1/2)² ≥ 1/2`, with equality only for
  `a = b = 0`, that is, for the square centred at `o`.
- **Two squares** (`Two/`). `phi a b ≤ 5/4` forces `a² + b² ≤ 1/4`, so each
  centre lies within `1/2` of `o`. By the parallelogram law the two centres are
  then at most 1 apart, while centres of interior-disjoint unit squares are at
  least 1 apart (`centers_distance_sq_ge_one`). A smaller disk is therefore
  impossible. At equality `o` is the midpoint of the two centres, and the
  equality case of the distance bound (`unit_contact`) puts the squares edge to
  edge: the rectangle.

## Three to five squares

Each lower bound is a proof by contradiction. Assume a packing with `R²` below
the target, relax the curved containment constraint to a strict polygon, then
show that `n` disjoint squares cannot all satisfy that polygon: each square
claims an arc of a small auxiliary circle around the disk centre, and the arcs
together would need more than the whole circle. For four squares the argument
also keeps the disk constraint `phi a b ≤ 2`.

### Step 1 — Contact tangents

`phi_le_of_contained`, `tangent_lt` (`Common/Basic.lean`, `Common/Tangents.lean`,
and `Tangents.lean` in the folders for three to five squares)

Write `a = |localX S o|`, `b = |localY S o|` for the disk centre `o` in a
square's own frame. The farthest vertex of the square is at squared distance

```lean
def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2
```

and containment of the four vertices gives `phi a b ≤ R²`. Since `phi` is
convex, `phi a b < R²` lies strictly on the inner side of the tangent line at
every point where `phi = R²`. Tangents at the contact points of the extremal
configuration give linear constraints on every square:

| n | target `R²` | contact points | strict polygon |
| --- | --- | --- | --- |
| 3 | `425/256` | `(1/2, 5/16)`, `(11/16, 0)` and their swaps | `P3Strict`, a 16-gon |
| 4 | `2` | `(1/2, 1/2)` | `P4Strict`: `a + b < 1`, a diamond |
| 5 | `5/2` | `(1, 0)`, `(0, 1)`, `((√5-1)/2, (√5-1)/2)` | `P5Strict`, a 12-gon |

(`p3_of_phi_lt`, `p4_of_phi_lt`, `p5_of_phi_lt`.) From here on the disk plays
no role for three and five squares.

### Step 2 — The angular budget

`OpenArc`, `open_arc_budget`, `uniform_arc_excess` (`Common/AngularBudget.lean`)

An `OpenArc o r U` is an angular interval, a centre direction and a half-width
in `(0, π]`, such that every point of the circle of radius `r` around `o` in
that interval lies in the planar region `U`. It certifies actual membership;
nothing is said about angular shadows. Disjoint regions carry disjoint arcs,
and the Haar measure on `AddCircle (2π)` gives

```text
Σ halfWidth ≤ π
```

Closed balls of radius `w ≤ π` have measure `2w`. Open arcs are handled by
shrinking every half-width by a common factor, so no boundary-measure argument
is needed. Consequently, if every one of `n` disjoint regions has half-width at
least `π/n` and one exceeds it, there is a contradiction.

### Step 3 — Exterior squares

`SquareChart`, `Common/RectangleArcs.lean`, `three_exterior_arc`,
`four_exterior_arc`, `five_exterior_arc`

A `SquareChart` reads a square's membership predicate in its own phase, with a
possible reversal of orientation and the two centre coordinates sorted so that
`b ≤ a`. For a square that does not contain `o`, an explicit
arcsine/arccosine interval of the auxiliary circle lies in its open interior:
for three and four squares the cap cut off by the near edge
(`SquareChart.cap_arc`), for five squares an interval that also meets the far
side (`cap_mem`). The polygon constraints and exact rational trigonometric
estimates show this arc is longer than `2π/n`:

| n | auxiliary radius | exterior arc |
| --- | --- | --- |
| 3 | `3/8` | `> 120°` |
| 4 | `1/2` | `> 90°`; this case also uses the disk, `phi a b ≤ 2` |
| 5 | `5/6` | `> 72°` |

If no square contains `o`, the budget is exceeded.

### Step 4 — The containing square

`four_containing_arc`, `five_containing_arc`, `ray_budget_impossible`,
`three_containing_impossible` (`Common/Regions.lean`, and `Containing.lean` in
the folders for three to five squares)

Disjointness allows at most one square to contain `o`, and its own arc on the
auxiliary circle may be short. For four and five squares it is replaced by its
*radial sweep* `openRay`: the union of its translates along the ray from `o`
through its centre, away from `o`. A Hahn–Banach separating functional for each
pair of squares (`support_separator`, `Common/Separation.lean`), together with
an octagon support estimate valid for every normal, shows that the sweep stays
disjoint from the other squares (`safe_openRay_of_disjoint`,
`Common/Support.lean`). No separating-axis enumeration is needed. The strict
octagon also keeps the containing square's centre away from `o`.

- **Four squares** (`Four/Containing.lean`). The sweep covers a quarter circle
  on every auxiliary circle of radius below `1/√2`, in particular on the circle
  of radius `1/2`. With three exterior arcs longer than `90°`, the budget fails
  (`ray_budget_impossible`).
- **Five squares** (`Five/Containing.lean`). The sweep contains a disk of
  radius `1/2` whose centre is at distance `1/√2` from `o`. That disk covers a
  `72°` arc of the circle of radius `5/6`, and with four exterior arcs longer
  than `72°`, the budget fails.
- **Three squares** (`Three/Containing.lean`). The sweep is too weak, and the
  argument measures the containing square itself. Let square `S` contain `o`,
  with sorted chart coordinates `b ≤ a < 1/2`, and let the other two be
  exterior. Only `S` needs the strict 16-gon; the other two need only the
  closed one, so the same argument serves uniqueness in Step 6.
  1. **Deficit.** On the circle of radius `3/8`, `S` contains an arc of length
     `L = π/2 + asin P + asin Q`, where `P = (1/2 - a)/(3/8)` and
     `Q = (1/2 - b)/(3/8)`. An exterior square with sorted chart coordinates
     `b' ≤ a'` contains a cap of length `min(2A, A + V)`, where
     `A = acos((a' - 1/2)/(3/8))` and `V = asin((1/2 - b')/(3/8))`, and this is
     at least `2π/3` (`three_cap_data`). The three-arc budget forces
     `L ≤ 2π/3`, and the contact tangents of `S` bound the deficit
     `δ = 2π/3 - L < 1/12` (`three_deficit_bounds`).
  2. **No clipped cap.** Disjointness from the disk inscribed in `S` gives a
     radial gap (`three_gap_from_containing`). If an exterior cap is clipped
     (`V < A`), monotonicity of `asin(1/2 + (16/13)t) - asin t` shows that it
     makes up the whole deficit, and the budget fails (`three_compensation`).
  3. **Full caps.** Both exterior caps are therefore symmetric about their
     square's radial phase, with `b' < 1/16` and `a' ≤ 11/16`
     (`three_cap_reduction`).
  4. **Angle between them.** Disjoint arcs have midpoints at least the sum of
     their half-widths apart, and three distances on the circle sum to at most
     `2π`. So the two radial phases differ by between `2π/3` and `2π/3 + 1/12`
     (`OpenArc.third_distance_bounds`).
  5. **Overlap.** For such an angle, the point `(1/5, ±2/5)` in the first
     exterior square's radial frame lies in both exterior squares
     (`near_axis_square_overlap`), which contradicts disjointness.

Together with Step 3 this proves `four_diamond_impossible` and, for every
choice of which square contains `o`, `three_polygon_strict_impossible`.
For five squares the argument even allows the closed 12-gon: it shows that
some square is centred exactly at `o` (`five_centered_square`), which the
strict 12-gon rules out (`five_polygon_strict_impossible`).

### Step 5 — Conclude

`Three.squared_lower`, `four_squared_lower`, `five_squared_lower`

`R²` below the squared radius puts every square in the strict polygon, which is
impossible (for four squares, together with `phi a b ≤ 2`). So the squared
radius is at most `R²`, and mathlib's `le_of_sq_le_sq` gives
`Three.radius ≤ R`, and likewise for four and five squares.

### Step 6 — Uniqueness

`Three.uniqueness`, `Four.uniqueness`, `Five.uniqueness`

At the optimal radius the lower-bound arguments run again with equality
allowed. Every inequality in the chain must then be tight, and the tight cases
are reconstructed exactly.

- **Five squares** (`Five/Uniqueness.lean`, `Common/Contacts.lean`). The
  closed 12-gon puts every centre within distance 1 of `o`, and by Step 4 one
  square is centred exactly at `o`. Centres of interior-disjoint unit squares
  are at least 1 apart, with equality only for parallel axes and a unit offset
  along an axis. The other four squares are therefore the four side-neighbours
  of the centred one: the plus. This uses only the closed 12-gon, not the disk
  (`Five.polygon_uniqueness`).
- **Four squares** (`Four/Uniqueness.lean`). The closed diamond alone is not
  rigid, so this case uses the disk. By Step 4 some square has `a + b ≥ 1`,
  and `phi a b ≤ 2` then forces `a = b = 1/2`: `o` is a vertex of that square
  and lies in no open square. On the circle of radius `1/2` each square holds
  an arc of at least `90°`, strictly more unless `a + b = 1`, so the budget
  makes `o` a vertex of all four squares. Their quarter-circle arcs have
  midpoints a quarter turn apart, which is the block.
- **Three squares** (`Three/Uniqueness.lean`). A square containing `o` keeps
  strict contact tangents even at the optimum (`p3_strict_of_inside`), and
  Step 4 asks only the closed 16-gon of the other two squares. So no square
  contains `o`, and the three exterior arcs of at least `120°` are each exactly
  `120°`. Equality leaves two contact types for the sorted chart coordinates:
  A = `(11/16, 0)`, with `o` on the square's axis, and B = `(1/2, 5/16)`, with
  `o` on the line of one of its edges. Two A-squares would overlap, and three
  B-squares would each hold a semicircle of the circle of radius `1/16`, so
  there is one A-square and two B-squares. The B-semicircles make the two
  B-phases antipodal and the three `120°` arcs make the midpoints equally
  spaced. Solving these angle equations puts the squares in the T slots, for
  every labelling and chart orientation.

## Legacy proof of three squares

The first formalization of the three-square case is on the
[`legacy`](https://github.com/vltanh/lean4-squares-in-circles/tree/legacy)
branch, with its own README and axiom audit. It normalizes a packing into a
fixed angle triangle, extracts separating axes, eliminates directed-chain
patterns to leave 48 branches, and bounds a trigonometric polynomial on each
branch with 53 rational certificates checked by `decide +kernel`. Its
`Cert.optimality` proves the lower bound of `Three.optimality`, stated with that
branch's `Packing` for `Fin 3` and its constant `optimalRadius`.

The occupied-arc proof replaced it as the main proof because a single framework
covers three, four and five squares and extends to uniqueness, and it needs no
case enumeration or certificate tables.
