# Definitions

[Back to the README](../README.md)

These definitions carry the entire meaning of the results. All except the radii
and the model centres are in `SquaresInCircles/Geometry.lean`.

## The plane

```lean
abbrev Point := ℝ × ℝ

def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)
```

A point is a pair of reals — the Euclidean plane in coordinates. `normSq p` is
the **squared** Euclidean length of `p`, and the statements measure distances
only with it, so `Real.sqrt` appears in them only in the radii. They never use
mathlib's `dist` on `ℝ × ℝ`, which is the maximum metric, not the Euclidean
one.

## Squares

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
- Storing the pair rather than an angle keeps the statement algebraic, with no
  branch cut and no ambiguity of `θ` modulo `2π`. Every `θ` gives such a
  pair, and every such pair comes from some `θ` (`frame_angle`), so nothing is
  lost. The proofs do use angles, as elements of `Real.Angle`, to parametrize
  circles.
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

## The disk

```lean
def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2
```

`p` lies within distance `R` of `o`, written squared to stay polynomial. Since
`‖p - o‖ ≤ R ⟺ ‖p - o‖² ≤ R²` when both sides are nonnegative, and `≤` is
non-strict, this is the **closed** disk. Note the squaring makes `inDisk o R p`
and `inDisk o (-R) p` agree, so the definition is only meaningful given
`0 ≤ R`, which `Packing` supplies.

## Packing

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

## The optimal radii

Each case defines its radius next to its optimal packing, and the root file
`SquaresInCircles.lean` collects them:

```lean
def One.radius : ℝ := Real.sqrt 2 / 2          -- One/Construction.lean
def Two.radius : ℝ := Real.sqrt 5 / 2          -- Two/Construction.lean
def Three.radius : ℝ := 5 * Real.sqrt 17 / 16  -- Three/Construction.lean
def Four.radius : ℝ := Real.sqrt 2             -- Four/Construction.lean
def Five.radius : ℝ := Real.sqrt (5 / 2)       -- Five/Construction.lean
def Seven.radius : ℝ := Real.sqrt 13 / 2       -- Seven/Construction.lean

def optimalRadius : ℕ → ℝ                      -- SquaresInCircles.lean
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 7 => Seven.radius
  | _ => 0
```

Each value is the distance from the disk centre to the outermost corners of the
optimal packing. Their squares `1/2`, `5/4`, `425/256`, `2`, `5/2` and `13/4`
are rational (`One.radius_sq`, …, `Five.radius_sq`, `Seven.radius_sq`). The
proofs bound the squared radius, so the contact inequalities stay polynomial,
which is what `nlinarith` needs; mathlib's `le_of_sq_le_sq` turns `r² ≤ R²`
into `r ≤ R` at the end.

## Normal forms

Uniqueness says that every packing at the optimal radius is the optimal packing,
moved by one rotation about the disk centre, with the squares relabelled. It is
stated about point sets:

```lean
abbrev Direction := Real.Angle

def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1 + phase.cos * x - phase.sin * y, o.2 + phase.sin * x + phase.cos * y)

abbrev openAxisSquare (c : Point) (x y : ℝ) : Prop :=
  |x - c.1| < 1 / 2 ∧ |y - c.2| < 1 / 2
abbrev closedAxisSquare (c : Point) (x y : ℝ) : Prop :=
  |x - c.1| ≤ 1 / 2 ∧ |y - c.2| ≤ 1 / 2

def HasNormalForm {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    (centers : Fin n → Point) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i x y,
    (openSquare (S (σ i)) (pointInDirection o φ x y) ↔ openAxisSquare (centers i) x y) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ x y) ↔ closedAxisSquare (centers i) x y)
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
| 7 | `(±1, ±1/2)`, `(0, -1)`, `(0, 0)`, `(0, 1)` | a column of three between two columns of two |

These are `One.centers`, …, `Five.centers` and `Seven.centers`;
`modelCenters n` selects the one for `n` (`SquaresInCircles.lean`). For
`n = 7` there is no uniqueness theorem: the middle column can slide, and
`Seven.centers` is the packing with the column centred. Each case builds its
optimal packing as `model i = axisSquare (centers i)`, the axis-parallel
square centred at `centers i`.

Read these definitions before trusting the result. A kernel check establishes
that the proofs are valid; it cannot establish that the statements mean what
you intend.
