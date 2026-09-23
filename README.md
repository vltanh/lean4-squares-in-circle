# Lean 4 formalization of packing unit squares in a disk

Machine-checked proofs, for `n = 1, …, 5`, of the smallest radius of a disk
that holds `n` non-overlapping unit squares, and that exactly one packing
attains it, up to rotation about the disk centre and relabelling of the squares.

| n | optimal radius | ≈ | the unique optimal packing |
| --- | --- | --- | --- |
| 1 | `√2 / 2` | 0.7071 | the square |
| 2 | `√5 / 2` | 1.1180 | a 2×1 rectangle |
| 3 | `5√17 / 16` | 1.2885 | the T |
| 4 | `√2` | 1.4142 | the 2×2 block |
| 5 | `√(5/2)` | 1.5811 | the plus |

- **Toolchain:** Lean `4.34.0`, mathlib `v4.34.0`
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound` only
- **Admissions:** none — no `sorry`, no `axiom`, no `native_decide`
- **Source:** 41 modules, ~5,400 lines

The earlier certificate-based proof of the three-square case is preserved on
the [`legacy`](https://github.com/vltanh/lean4-squares-in-circles/tree/legacy)
branch; see [Legacy proof](#legacy-proof).

## Results

The results for all five cases are in the root file `SquaresInCircles.lean`,
namespace `SquaresInCircles`:

```lean
theorem optimality (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    optimalRadius n ≤ R

theorem attainment (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5) :
    ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n)

theorem uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    HasNormalForm S o (modelCenters n)
```

`optimality_attainment_uniqueness` conjoins the three. Each theorem states its
content directly; there is no intermediate abbreviation to unfold.

Each case also stands alone, in namespaces `SquaresInCircles.One`, …,
`SquaresInCircles.Five` (folders `One/`, …, `Five/`), with the same theorems:

| theorem | statement, for `n = 3` |
| --- | --- |
| `Three.optimality` | `Packing S o R → Three.radius ≤ R` |
| `Three.attainment` | `∃ S o, Packing S o Three.radius` |
| `Three.optimality_and_attainment` | both of the above |
| `Three.uniqueness` | `Packing S o Three.radius → HasNormalForm S o Three.centers` |
| `Three.rigid_uniqueness` | the same, with an explicit isometry of the plane |

`rigid_uniqueness` gives a bijection of the plane that preserves Euclidean
distance and takes the origin to `o`, under which the closed squares are exactly
the model squares. `Five.polygon_uniqueness` needs only interior-disjointness
and the closed 12-gon of Step 1, not the disk.

**Polygon relaxations.** For three, four and five squares the proofs go through
stronger statements that mention no disk at all:
`three_polygon_strict_impossible`, `four_polygon_strict_impossible` and
`five_polygon_strict_impossible` rule out `n` interior-disjoint squares whose
centres all satisfy the strict contact polygon of Step 1.

## Definitions

These definitions carry the entire meaning of the results. All except the radii
and the normal forms are in `SquaresInCircles/Geometry.lean`.

### The plane

```lean
abbrev Point := ℝ × ℝ

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)
```

A point is a pair of reals — the Euclidean plane in coordinates, with no
additional structure. `normSq p` is the **squared** length of `p`; working with
squares throughout avoids `Real.sqrt` in the geometry, and the square root
appears only where the radius itself is stated.

### Squares

```lean
structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1
```

A square is a centre plus an orientation. The orientation is stored as the pair
`(cosine, sine)` rather than as an angle `θ`:

- `unit` forces `cosine² + sine² = 1`, so the vectors `(cosine, sine)` and
  `(-sine, cosine)` are unit length and perpendicular. They are the square's own
  axes — an **orthonormal frame**.
- Storing the pair rather than an angle keeps everything algebraic. The proofs
  need `cos θ` and `sin θ`, never `θ` itself, so this avoids branch cuts and
  the ambiguity of `θ` modulo `2π`. Every `θ` gives such a pair, and every such
  pair comes from some `θ`, so nothing is lost.
- The fields are per-square, so the squares rotate **independently**.

```lean
def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)

def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)
```

`localX`/`localY` give the coordinates of `p` in the square's own frame:
translate so the centre is the origin, then project onto the two axes. Because
the frame is orthonormal this is a rigid change of coordinates — it preserves
distances, so a set that is a unit square in local coordinates is a unit square
in the plane.

```lean
def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2

def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2
```

In local coordinates the square is the box `[-1/2, 1/2]²`, whose side is
`1/2 - (-1/2) = 1` — genuinely a **unit** square. The two versions differ only
in strictness: `closedSquare` includes the boundary, `openSquare` is the
interior. Non-overlap is stated with `openSquare`, so squares may touch along
edges or at corners but may not share interior area. Every optimal packing
but the single square relies on this.

### The disk

```lean
def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2
```

`p` lies within distance `R` of `o`, written squared to stay polynomial. Since
`‖p - o‖ ≤ R ⟺ ‖p - o‖² ≤ R²` when both sides are nonnegative, and `≤` is
non-strict, this is the **closed** disk. Note the squaring makes `inDisk o R p`
and `inDisk o (-R) p` agree, so the definition is only meaningful given
`0 ≤ R`, which `Packing` supplies.

### Packing

```lean
def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))
```

Three conditions, and nothing else:

- `0 ≤ R` — the radius is nonnegative.
- **Containment** — every point of every closed square lies in the disk.
  Stated with `closedSquare`, so boundaries must fit too.
- **Non-overlap** — no point is interior to two distinct squares.

What the encoding does and does not assume:

- `S : Fin n → UnitSquare` is an arbitrary family, each square with its own
  frame, so the squares are independently placed and independently rotated.
- `o` and `R` are universally quantified in the theorems, so the disk centre
  ranges over the whole plane and no relationship between centre and squares is
  presupposed.
- No orientation, separating-axis, arc, tangent, or lower-bound assumption
  appears anywhere in the hypothesis. Those are derived in the proof, not
  assumed in the statement.

### The optimal radii

Each case defines its radius next to its optimal packing, and the root file
`SquaresInCircles.lean` collects them:

```lean
def One.radius : ℝ := Real.sqrt 2 / 2          -- One/Construction.lean
def Two.radius : ℝ := Real.sqrt 5 / 2          -- Two/Construction.lean
def Three.radius : ℝ := 5 * Real.sqrt 17 / 16  -- Three/Construction.lean
def Four.radius : ℝ := Real.sqrt 2             -- Four/Construction.lean
def Five.radius : ℝ := Real.sqrt (5 / 2)       -- Five/Construction.lean

def optimalRadius : ℕ → ℝ                      -- SquaresInCircles.lean
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | _ => 0
```

Each value is the distance from the disk centre to the outermost corners of the
optimal packing. Their squares `1/2`, `5/4`, `425/256`, `2` and `5/2` are
rational (`One.radius_sq`, …, `Five.radius_sq`). The proofs work with squared
lengths so the contact inequalities stay polynomial, which is what `nlinarith`
needs. `Real.sqrt` enters only at the last step, where
`radius_lower_of_squared` (`Common/Basic.lean`) turns `r² ≤ R²` into `r ≤ R`.

### Normal forms

Uniqueness is stated about point sets (`Common/NormalForm.lean`,
`Common/Coordinates.lean`):

```lean
def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1+phase.cos*x-phase.sin*y, o.2+phase.sin*x+phase.cos*y)

abbrev OpenRect (c : Point) (x y : ℝ) : Prop := |x-c.1| < 1/2 ∧ |y-c.2| < 1/2
abbrev ClosedRect (c : Point) (x y : ℝ) : Prop := |x-c.1| ≤ 1/2 ∧ |y-c.2| ≤ 1/2

def HasNormalForm {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    (centers : Fin n → Point) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i x y,
    (openSquare (S (σ i)) (pointInDirection o φ x y) ↔ OpenRect (centers i) x y) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ x y) ↔ ClosedRect (centers i) x y)
```

`pointInDirection o φ` reads coordinates `(x, y)` in the frame at the disk
centre `o`, rotated by `φ`. `HasNormalForm` says that in one such frame, after
relabelling by `σ`, square `σ i` is exactly the axis-parallel unit square
centred at `centers i`, both as an open and as a closed set. It compares point
sets rather than `UnitSquare` records, because a quarter-turn of a frame
describes the same square. No reflection is needed, since each model is
symmetric under one. With the disk centre at the origin, the models are:

| n | `centers` | packing |
| --- | --- | --- |
| 1 | `(0, 0)` | the square |
| 2 | `(-1/2, 0)`, `(1/2, 0)` | the 2×1 rectangle |
| 3 | `(-1/2, -5/16)`, `(1/2, -5/16)`, `(0, 11/16)` | the T |
| 4 | `(±1/2, ±1/2)` | the 2×2 block |
| 5 | `(0, 0)`, `(±1, 0)`, `(0, ±1)` | the plus |

These are `One.centers`, …, `Five.centers`; `modelCenters n` selects the one for
`n` (`SquaresInCircles.lean`).

Read these definitions before trusting the result. A kernel check establishes
that the proofs are valid; it cannot establish that the statements mean what
you intend.

## Proof outline

### One and two squares

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

### Three to five squares

Each lower bound is a proof by contradiction. Assume a packing with `R²` below
the target, relax the curved containment constraint to a strict polygon, then
show that `n` disjoint squares cannot all satisfy that polygon: each square
claims an arc of a small auxiliary circle around the disk centre, and the arcs
together would need more than the whole circle.

#### Step 1 — Contact tangents

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
no role.

#### Step 2 — The angular budget

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

#### Step 3 — Exterior squares

`SquareChart`, `Common/RectangleArcs.lean`, `three_exterior_arc`,
`four_exterior_arc`, `five_exterior_arc`

A `SquareChart` reads a square's membership predicate in its own phase, with a
possible reversal of orientation and the two centre coordinates sorted so that
`b ≤ a`. For a square that does not contain `o`, an explicit
arcsine/arccosine interval of the auxiliary circle lies in its open interior.
The polygon constraints and exact rational trigonometric estimates show this
arc is longer than `2π/n`:

| n | auxiliary radius | exterior arc |
| --- | --- | --- |
| 3 | `3/8` | `> 120°` |
| 4 | one `r` strictly between `1/2` and `1/√2`, chosen per configuration (`common_four_radius`) | `> 90°` |
| 5 | `5/6` | `> 72°` |

If no square contains `o`, the budget is exceeded. Disjointness allows at most
one square to contain `o`.

#### Step 4 — The containing square, four and five squares

`support_separator`, `safe_openRay_of_disjoint`, `four_containing_arc`,
`five_containing_arc`

The square containing `o` is replaced by its *radial sweep* `openRay`: the union
of its translates along the ray from `o` through its centre, away from `o`. A
Hahn–Banach separating functional for each pair of squares
(`support_separator`, `Common/Separation.lean`), together with an octagon support
estimate valid for every normal, shows that the sweep stays disjoint from the
other squares. No separating-axis enumeration is needed. The strict octagon
also forces the containing square's centre to differ from `o`.

- **Four squares.** The sweep covers a quarter circle on every auxiliary circle
  of radius below `1/√2`. With three exterior arcs longer than `90°`, the
  budget fails.
- **Five squares.** The sweep contains a disk of radius `1/2` whose centre is at
  distance `1/√2` from `o`. That disk covers a `72°` arc of the circle of radius
  `5/6`, and with four exterior arcs longer than `72°`, the budget fails.

#### Step 5 — The containing square, three squares

`three_containing_impossible` (`Three/Containing.lean`)

For three squares the sweep is too weak, and the argument measures the
containing square itself. Let square `S` contain `o`, with sorted chart
coordinates `b ≤ a < 1/2`, and let the other two be exterior.

1. **Deficit.** On the circle of radius `3/8`, `S` contains an arc of length
   `L = π/2 + asin P + asin Q`, where `P = (1/2 - a)/(3/8)` and
   `Q = (1/2 - b)/(3/8)`. An exterior square with sorted chart coordinates
   `b' ≤ a'` contains a cap of length `min(2A, A + V)`, where
   `A = acos((a' - 1/2)/(3/8))` and `V = asin((1/2 - b')/(3/8))`, and this is
   more than `2π/3`. The three-arc budget
   forces `L < 2π/3`, and the contact tangents bound the deficit
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
5. **Overlap.** For such an angle, the point `(1/5, ±2/5)` in the first exterior
   square's radial frame lies in both exterior squares
   (`near_axis_square_overlap`), which contradicts disjointness.

Together with Step 3 this proves `three_polygon_strict_impossible`, for every
choice of which square contains `o`.

#### Step 6 — Conclude

`Three.squared_lower`, `four_squared_lower`, `five_squared_lower`

`R²` below the squared radius puts every square in the strict polygon, which is
impossible. So the squared radius is at most `R²`, and `radius_lower_of_squared`
gives `Three.radius ≤ R`, and likewise for four and five squares.

#### Step 7 — Uniqueness

`Three.uniqueness`, `Four.uniqueness`, `Five.uniqueness`

At the optimal radius the lower-bound arguments run again with equality
allowed. Every inequality in the chain must then be tight, and the tight cases
are reconstructed exactly.

- **Five squares** (`Five/Uniqueness.lean`, `Common/Contacts.lean`). The
  closed 12-gon puts every centre within distance 1 of `o`. If no square were
  centred at `o`, the exterior arcs (still longer than `72°`) and the sweep of a
  containing square (`72°`) would overfill the circle, so one square is centred
  exactly at `o`. Centres of interior-disjoint unit squares are at least 1
  apart, with equality only for parallel axes and a unit offset along an axis.
  The other four squares are therefore the four side-neighbours of the centred
  one: the plus. This uses only the closed 12-gon, not the disk
  (`Five.polygon_uniqueness`).
- **Four squares** (`Four/Uniqueness.lean`). The closed diamond alone is not
  rigid, so this case uses the disk. The strict Diamond Lemma leaves a square
  with `a + b ≥ 1`, and `phi a b ≤ 2` then forces `a = b = 1/2`: `o` is a vertex
  of that square and lies in no open square. On the circle of radius `1/2` each
  square holds an arc of at least `90°`, strictly more unless `a + b = 1`, so
  the budget makes `o` a vertex of all four squares. Their quarter-circle arcs
  have midpoints a quarter turn apart, which is the block.
- **Three squares** (`Three/Uniqueness.lean`). A square
  containing `o` keeps strict contact tangents even at the optimum, and the
  Step 5 argument still refutes it when the other two squares satisfy only the
  closed 16-gon. So no square contains `o`, and the three exterior arcs of at
  least `120°` are each exactly `120°`. Equality leaves two contact types for
  the sorted chart coordinates: A = `(11/16, 0)`, with `o` on the square's axis,
  and B = `(1/2, 5/16)`, with `o` on the line of one of its edges. Two A-squares
  would overlap, and three B-squares would each hold a semicircle of the circle
  of radius `1/16`, so there is one A-square and two B-squares. The
  B-semicircles make the two B-phases antipodal and the three `120°` arcs make
  the midpoints equally spaced. Solving these angle equations puts the squares
  in the T slots, for every labelling and chart orientation.

## Layout

```text
SquaresInCircles.lean      optimalRadius, and all five cases in one statement
SquaresInCircles/
├── Geometry.lean          points, squares, disks, Packing
├── Common/                tools shared by several cases
├── One/                   n = 1
├── Two/                   n = 2
├── Three/                 n = 3
├── Four/                  n = 4
└── Five/                  n = 5
```

Every case folder has the same three core files: `Construction.lean` (the
radius, the optimal packing and its centres), `Optimality.lean` (the lower
bound) and `Uniqueness.lean`. Three, four and five squares add the same three
helper files for the arc argument: `Tangents.lean` (the contact polygon),
`Exterior.lean` (arcs of the squares that do not contain the disk centre) and
`Containing.lean` (the square that does). No case imports another: each
imports only `Common/` and its own folder.

### `Common/`

| File | Contents |
| --- | --- |
| `Basic.lean` | Square frames, the farthest-vertex bound `phi`, centre distances, `radius_lower_of_squared` |
| `Tangents.lean` | Tangent identity; the octagon shared by four and five squares |
| `Separation.lean` | Hahn–Banach supporting functional for two squares with disjoint interiors |
| `Support.lean` | Octagon support for every normal; the radial sweep stays disjoint |
| `AngularBudget.lean` | `OpenArc` witnesses and the Haar-measure budget |
| `ArcMetric.lean` | Midpoint separation of disjoint arcs; circle perimeter inequality |
| `Charts.lean` | `SquareChart`: membership in a square's own phase, sorted coordinates |
| `Coordinates.lean` | Points in a rotated frame; inscribed disks; symmetric caps |
| `Regions.lean` | Disjoint regions, with the containing square replaced by its sweep |
| `ElementaryTrig.lean` | Arcsine and cosine estimates with exact rational constants |
| `RectangleArcs.lean` | The occupied arc of an exterior square |
| `Constructions.lean` | Disjointness and containment of axis-parallel squares |
| `NormalForm.lean` | `HasNormalForm`, the rigid-motion witness, slots to a permutation |
| `Angles.lean` | Quarter turns of a frame; four directions a quarter turn apart |
| `Contacts.lean` | Disjoint squares have centres at least 1 apart; equality means side-neighbours |

### The cases

| File | One | Two | Three | Four | Five |
| --- | --- | --- | --- | --- | --- |
| `Construction.lean` | the centred square | the 2×1 rectangle | the T | the 2×2 block | the plus |
| `Tangents.lean` | | | the 16-gon | the diamond | the 12-gon |
| `Exterior.lean` | | | arcs over `120°`; some square contains `o` | arcs over `90°`, common radius | arcs over `72°` |
| `Containing.lean` | | | deficit, compensation, overlap point | the sweep covers a quarter circle | the sweep covers a `72°` arc |
| `Optimality.lean` | half-diagonal bound | centre-distance bound | strict 16-gon infeasibility | strict diamond infeasibility | strict 12-gon infeasibility |
| `Uniqueness.lean` | centred at `o` | edge to edge, `o` the midpoint | closed caps, contact types, the T | `o` a vertex of every square | a square centred at `o`, closed 12-gon rigidity |

Each `Construction.lean` also defines the case's `radius` and its `centers`, the
optimal packing in the frame of its disk centre.

## Verification

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SanityChecks.lean
```

Requires Elan/Lake and network access for mathlib.

- `lake build` must report zero `declaration uses 'sorry'` warnings.
- Every `#print axioms` line in the audit must read exactly
  `[propext, Classical.choice, Quot.sound]`.
- `sorryAx` in that output would indicate an unproved lemma;
  `Lean.ofReduceBool` would indicate `native_decide` and compiler trust.
- The audit also prints `Packing`, `optimalRadius`, `HasNormalForm`,
  `modelCenters` and the theorem signatures for inspection.
- `SanityChecks.lean` checks the radius table, re-proves the exact rational
  margins the proofs rely on, restates the public theorems, and checks all five
  optimal packings against their normal forms; it must elaborate without
  errors.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved.

**Trusted base:** Lean, Lake, mathlib. Every numeric margin is an exact rational
inequality closed by `norm_num`, `linarith` or `nlinarith`; `π` enters only
through mathlib's rational bounds `3.14 < π < 3.1416`. There are no
machine-generated certificates.

## Legacy proof

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

## License

Apache-2.0, matching mathlib and the Lean ecosystem.

## Contributors

This formalization was produced by AI models working in sequence.

**Legacy certificate proof.** ChatGPT 6 Pro supplied the mathematics and the
initial Lean development. Claude Opus 5 High-Max ported it to Lean `4.34.0` /
mathlib `v4.34.0`, fixed the errors that surfaced once it was compiled, and
arranged the repository. ChatGPT's informal argument, Python certificate
verifier and three Lean drafts are preserved verbatim in `reference/` on the
`legacy` branch; they play no part in the Lean verification path.

**Occupied-arc proof.** Following an idea from Claude Opus 5 Max, ChatGPT 6
Pro wrote the proof for three, four and five squares and the draft Lean
development, submitted uncompiled as
[PR #2](https://github.com/vltanh/lean4-squares-in-circles/pull/2).
Claude Opus 5.5 Max cleaned it up. It compiled the draft against Lean
`4.34.0` / mathlib `v4.34.0`, with repairs covering library renames, tactic
normal forms and the missing measure instance on `Real.Angle`; no theorem
statement changed. It then separated the proof from the certificate modules
and made it the main proof.

**Uniqueness.** ChatGPT 6 Pro wrote the uniqueness proofs for three, four and
five squares and the draft Lean development, submitted uncompiled as
[PR #3](https://github.com/vltanh/lean4-squares-in-circles/pull/3).
Claude Opus 5.5 Max compiled it against Lean `4.34.0` / mathlib `v4.34.0`, with
repairs covering library interfaces, tactic normal forms and the reduction of
vector literals; no public statement changed. It then integrated the uniqueness
theorems into the main proof.

**One and two squares.** Claude Opus 5.5 Max added the cases `n = 1` and
`n = 2`, and reorganized the library by `n` as `SquaresInCircles`.

Direction, review and the decisions about scope and naming were the
repository owner's.
