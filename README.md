# Lean 4 formalization of packing three unit squares in a disk

A machine-checked proof that the smallest disk containing three
non-overlapping unit squares has radius `5 * Real.sqrt 17 / 16 ≈ 1.2884705`.
The same occupied-arc framework also settles four squares (radius `√2`) and
five squares (radius `√(5/2)`).

- **Toolchain:** Lean `4.34.0`, mathlib `v4.34.0`
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound` only
- **Admissions:** none — no `sorry`, no `axiom`, no `native_decide`
- **Source:** 28 modules, ~3,400 lines

The earlier certificate-based proof of the three-square result is preserved on
the [`legacy`](https://github.com/vltanh/three-unit-squares-in-circle/tree/legacy)
branch; see [Legacy proof](#legacy-proof).

## Results

**Three squares.** `optimality` and `optimality_and_attainment` are in
`ThreeUnitSquaresInCircle/ThreeArc.lean`, namespace
`ThreeUnitSquaresInCircle.ThreeArc`. Every packing of three unit squares in a
disk of radius `R` satisfies `optimalRadius ≤ R`:

```lean
theorem optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius ≤ R
```

An explicit T-shaped arrangement realizes the bound
(`ThreeUnitSquaresInCircle/Construction.lean`, namespace
`ThreeUnitSquaresInCircle`):

```lean
theorem exists_packing_at_optimum :
    ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o optimalRadius
```

`optimality_and_attainment` conjoins the two. Each theorem states its content
directly; there is no intermediate abbreviation to unfold.

**Four and five squares.** In namespace `ThreeUnitSquaresInCircle.Unified`
(`Unified/Four.lean`, `Unified/Five.lean`):

```lean
theorem four_optimality (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : Real.sqrt 2 ≤ R

theorem five_optimality (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : Real.sqrt ((5:ℝ)/2) ≤ R
```

The 2×2 block and the plus arrangement attain these (`block_packing`,
`plus_packing` in `Unified/Constructions.lean`).
`optimality_and_attainment_345` (`Unified/Main.lean`) states lower bound and
attainment together for `n = 3, 4, 5`. No uniqueness or equality
classification is claimed.

**Polygon relaxations.** The proofs go through stronger statements that
mention no disk at all: `three_polygon_strict_impossible`,
`four_polygon_strict_impossible` and `five_polygon_strict_impossible` rule out
`n` interior-disjoint squares whose centres all satisfy the strict contact
polygon of the next section.

## Definitions

These definitions carry the entire meaning of the result. All except
`PackingN` are in `ThreeUnitSquaresInCircle/Geometry.lean`.

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
- The fields are per-square, so the three squares rotate **independently**.

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
edges or at corners but may not share interior area. The T arrangement relies
on this.

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

### The optimal radius

```lean
def optimalRadius : ℝ := 5 * Real.sqrt 17 / 16
def targetSq : ℝ := 425 / 256
```

`optimalRadius ≈ 1.2884705` is the value the theorems establish, and `targetSq`
is its square: `(5√17/16)² = 25·17/256 = 425/256`, proved as `optimalRadius_sq`.

Both exist because `optimalRadius` is irrational while `targetSq` is rational.
The proof works with squared lengths so the contact inequalities stay
polynomial, which is what `nlinarith` needs. `Real.sqrt` enters only at the
last step, where `radius_lower_of_squared` turns `targetSq ≤ R²` into
`optimalRadius ≤ R`.

### Packing

```lean
def Packing (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ) : Prop :=
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

- `S : Fin 3 → UnitSquare` is an arbitrary triple, each with its own frame, so
  the squares are independently placed and independently rotated.
- `o` and `R` are universally quantified in the theorem, so the disk centre
  ranges over the whole plane and no relationship between centre and squares is
  presupposed.
- No orientation, separating-axis, arc, tangent, or lower-bound assumption
  appears anywhere in the hypothesis. Those are derived in the proof, not
  assumed in the statement.

For four and five squares the same predicate is stated for any family size
(`ThreeUnitSquaresInCircle/Unified/Basic.lean`):

```lean
def PackingN {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))
```

`PackingN S o R ↔ Packing S o R` holds by `Iff.rfl` for `S : Fin 3 → UnitSquare`.

Read these definitions before trusting the result. A kernel check establishes
that the proofs are valid; it cannot establish that the statements mean what
you intend.

## Proof outline

Each lower bound is a proof by contradiction. Assume a packing with `R²` below
the target, relax the curved containment constraint to a strict polygon, then
show that `n` disjoint squares cannot all satisfy that polygon: each square
claims an arc of a small auxiliary circle around the disk centre, and the arcs
together would need more than the whole circle.

### Step 1 — Contact tangents

`phi_le_of_contained`, `tangent_lt` (`Unified/Basic.lean`, `Unified/Tangents.lean`)

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

### Step 2 — The angular budget

`OpenArc`, `open_arc_budget`, `uniform_arc_excess` (`Unified/AngularBudget.lean`)

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

`SquareChart`, `RectangleArcs.lean`, `three_exterior_arc`, `four_exterior_arc`,
`five_exterior_arc`

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

### Step 4 — The containing square, four and five squares

`support_separator`, `safe_openRay_of_disjoint`, `four_containing_arc`,
`five_containing_arc`

The square containing `o` is replaced by its *radial sweep* `openRay`: the union
of its translates along the ray from `o` through its centre, away from `o`. A
Hahn–Banach separating functional for each pair of squares
(`support_separator`, `Separation.lean`), together with an octagon support
estimate valid for every normal, shows that the sweep stays disjoint from the
other squares. No separating-axis enumeration is needed. The strict octagon
also forces the containing square's centre to differ from `o`.

- **Four squares.** The sweep covers a quarter circle on every auxiliary circle
  of radius below `1/√2`. With three exterior arcs longer than `90°`, the
  budget fails.
- **Five squares.** The sweep contains a disk of radius `1/2` whose centre is at
  distance `1/√2` from `o`. That disk covers a `72°` arc of the circle of radius
  `5/6`, and with four exterior arcs longer than `72°`, the budget fails.

### Step 5 — The containing square, three squares

`three_containing_impossible` (`Unified/ThreeContaining.lean`)

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

### Step 6 — Conclude

`ThreeArc.squared_lower`, `four_squared_lower`, `five_squared_lower`

`R²` below the target puts every square in the strict polygon, which is
impossible. So `targetSq ≤ R²`, and `radius_lower_of_squared` gives
`optimalRadius ≤ R`. The four- and five-square bounds conclude the same way with
`Real.sqrt`.

## Modules

### Problem statement and shared tools

| File | Contents |
| --- | --- |
| `Geometry.lean` | Unit squares, disk containment, interior non-overlap, `optimalRadius` |
| `Separation.lean` | Hahn–Banach supporting functional for two squares with disjoint interiors |
| `Construction.lean` | The T arrangement: containment, disjointness, attainment |

### Arc framework (`Unified/`)

| File | Contents |
| --- | --- |
| `Basic.lean` | `PackingN`, square frames, farthest-vertex bound |
| `Tangents.lean` | Tangent identity; the 16-gon, diamond, octagon and 12-gon |
| `Support.lean` | Octagon support for every normal; the sweep stays disjoint |
| `AngularBudget.lean` | `OpenArc` witnesses and the Haar-measure budget |
| `ArcMetric.lean` | Midpoint separation of disjoint arcs; circle perimeter inequality |
| `Charts.lean` | `SquareChart`: membership in a square's own phase, sorted coordinates |
| `Regions.lean` | Disjoint regions, with the containing square replaced by its sweep |
| `ElementaryTrig.lean` | Arcsine and cosine estimates with exact rational constants |
| `RectangleArcs.lean` | The occupied arc of an exterior square |

### Four and five squares

| File | Contents |
| --- | --- |
| `FourScalar.lean` | Common auxiliary radius; exterior arcs longer than `90°` |
| `FourRay.lean` | The sweep of the containing square covers a quarter circle |
| `Four.lean` | Strict diamond infeasibility; `four_optimality` |
| `FiveScalar.lean` | Radius `5/6`; exterior arcs longer than `72°` |
| `RadialDisk.lean` | The sweep of the containing square covers a `72°` arc |
| `Five.lean` | Strict 12-gon infeasibility; `five_optimality` |
| `Constructions.lean` | The block and plus packings |

### Three squares

| File | Contents |
| --- | --- |
| `ThreeExterior.lean` | Exterior arcs longer than `120°`; some square contains `o` |
| `ThreeCoordinates.lean` | Cartesian membership from charts; the explicit overlap point |
| `ThreeScalar.lean` | Deficit bound and compensation inequality |
| `ThreeCaps.lean` | Arc witnesses for the containing square and the exterior caps |
| `ThreeContaining.lean` | The containing case; `three_polygon_strict_impossible` |
| `ThreeArc.lean` | End-to-end assembly: `optimality`, `optimality_and_attainment` |
| `Unified/Main.lean` | `optimality_and_attainment_345` for `n = 3, 4, 5` |

`ThreeUnitSquaresInCircle/ThreeArc.lean` does not import the four- or
five-square modules.

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
- The audit also prints `Packing`, `PackingN` and the theorem signatures for
  inspection.
- `SanityChecks.lean` re-proves the exact rational margins the proof relies on
  and restates the public theorems; it must elaborate without errors.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved.

**Trusted base:** Lean, Lake, mathlib. Every numeric margin is an exact rational
inequality closed by `norm_num`, `linarith` or `nlinarith`; `π` enters only
through mathlib's rational bounds `3.14 < π < 3.1416`. There are no
machine-generated certificates.

## Legacy proof

The first formalization of the three-square result is on the
[`legacy`](https://github.com/vltanh/three-unit-squares-in-circle/tree/legacy)
branch, with its own README and axiom audit. It normalizes a packing into a
fixed angle triangle, extracts separating axes, eliminates directed-chain
patterns to leave 48 branches, and bounds a trigonometric polynomial on each
branch with 53 rational certificates checked by `decide +kernel`. Its
`Cert.optimality` proves the same statement as `ThreeArc.optimality`, over the
same `Geometry.lean`.

The occupied-arc proof replaced it as the main proof because a single framework
covers three, four and five squares, and it needs no case enumeration or
certificate tables.

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
[PR #2](https://github.com/vltanh/three-unit-squares-in-circle/pull/2).
Claude Opus 5.5 Max cleaned it up. It compiled the draft against Lean
`4.34.0` / mathlib `v4.34.0`, with repairs covering library renames, tactic
normal forms and the missing measure instance on `Real.Angle`; no theorem
statement changed. It then separated the proof from the certificate modules
and made it the main proof.

Direction, review and the decisions about scope and naming were the
repository owner's.
