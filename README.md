# Lean 4 formalization of packing three unit squares in a disk

> **Legacy proof.** This branch preserves the original certificate-based
> formalization. The [`main`](https://github.com/vltanh/three-unit-squares-in-circle/tree/main)
> branch now carries the occupied-arc proof, which proves the same statement
> over the same `Geometry.lean` and extends to four and five squares.

A machine-checked proof that the smallest disk containing three
non-overlapping unit squares has radius `5 * Real.sqrt 17 / 16 ≈ 1.2884705`.

- **Toolchain:** Lean `4.34.0`, mathlib `v4.34.0`
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound` only
- **Admissions:** none — no `sorry`, no `axiom`, no `native_decide`
- **Source:** 19 modules, ~3,600 lines

## Results

`optimality` and `optimality_and_attainment` are in
`ThreeUnitSquaresInCircle/Main.lean`, namespace `ThreeUnitSquaresInCircle.Cert`.
`exists_packing_at_optimum` is in `Construction.lean`, namespace
`ThreeUnitSquaresInCircle`.

**Lower bound.** Every packing of three unit squares in a disk of radius `R`
satisfies `optimalRadius ≤ R`:

```lean
theorem optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius ≤ R
```

**Attainment.** An explicit T-shaped arrangement realizes the bound
(`ThreeUnitSquaresInCircle/Construction.lean`):

```lean
theorem exists_packing_at_optimum :
    ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o optimalRadius
```

`optimality_and_attainment` conjoins the two. Each theorem states its content
directly; there is no intermediate abbreviation to unfold.

## Definitions

These definitions carry the entire meaning of the result. All are in
`ThreeUnitSquaresInCircle/Geometry.lean`.

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
The proof works with squared lengths throughout so every step stays polynomial,
which is what `nlinarith`, the rational certificates and `decide +kernel`
require. `Real.sqrt` enters only at the last step, where
`radius_lower_of_squared` turns `targetSq ≤ R²` into `optimalRadius ≤ R`.

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
- No certificate-existence, orientation, separating-axis, or lower-bound
  assumption appears anywhere in the hypothesis. Those are derived in the proof,
  not assumed in the statement.

Read these definitions before trusting the result. A kernel check establishes
that the proofs are valid; it cannot establish that the statements mean what
you intend.

## Proof outline

The argument is a proof by contradiction. Assume a packing with
`R² < targetSq`, reduce it to one of finitely many configurations, and derive
two incompatible bounds on the same quantity. `Main.lean` is the assembly; each
step below names the theorem that performs it.

### Strategy

An arbitrary packing has too many degrees of freedom to attack directly: three
centres, three rotations, and a disk centre. Steps 1–4 remove almost all of
them. What survives is a **pair of angles** ranging over a triangle, together
with a choice from a **finite** set of combinatorial branches. Steps 5–7 then
bound a single function of that angle pair from both sides.

The function is `polynomial c x`, a trigonometric polynomial in the angle pair
`x` determined by a *certificate* `c`. A certificate is rational data —
multipliers, weights and coefficients — whose validity is a finite arithmetic
check (`arithmeticValid`, decided in the kernel). The final contradiction is
`targetSq ≤ polynomial (table i) x ≤ R² < targetSq`.

### Step 1 — Normalize the configuration

`normalize_orientations` (`OrientationNormalization.lean`, `PlaneTools.lean`)

Given `Packing S o R`, produce centres `c` and an angle pair `x` with

```lean
AngleDomain.Domain x.1 x.2 ∧ Packing (angularSquares c x) (0,0) R
```

Translation moves the disk centre to the origin. Each square's frame is
represented by an angle modulo `π/2` (a square is invariant under quarter
turns), the three angles are sorted, and the configuration is cut at the
largest cyclic gap and reflected if needed. The result lands in the domain
triangle `0 ≤ a ∧ 2a ≤ b ∧ 2b - a ≤ 1/2`, in units of `π`.

The first square's angle is normalized to `0`, so only two angles remain free.
Every operation used is a rigid motion or relabelling, so `Packing` is
preserved in both directions — this is a genuine reduction, not an added
hypothesis.

### Step 2 — Extract separating axes

`choose_separating_axes` (`SeparatingAxes.lean`, `AxisSelection.lean`)

Two convex bodies with disjoint interiors admit a separating line. For squares
the separating direction can be taken to be an edge normal of one of them.
`support_separator` derives this from a supporting functional, and the result
is a *signed* inequality per pair: for each edge `e` of the triangle of
squares,

```lean
∀ e, widths x e ≤ dot (normal x k s e)
  (sub (c' (edgeEnd e)) (c' (edgeStart e)))
```

The data extracted is `k : Fin 3 → Fin 4`, recording which of the four cardinal
directions each separating normal points along, and `s : Fin 3 → Fin 3`,
recording which square contributed it. A common quarter-turn normalizes
`k 0 = 0`, leaving `(k 1, k 2)` as the only combinatorial freedom: `4 × 4 = 16`
patterns.

### Step 3 — Eliminate chain patterns

`forbidden_chain` (`ForbiddenChain.lean`, `Arithmetic.lean`)

A *chain* is three distinct squares `i, j, k` whose successive separating
normals point the same way:

```lean
def hasChain (k02 k12 : Fin 4) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    direction k02 k12 i j = direction k02 k12 j k
```

A chain forces the three centres to spread out along one direction. Two bounds
collide:

- **Upper** — all centres lie within `11/16` of the disk centre
  (`square_center_bound`, from the farthest-vertex formula and
  `R² ≤ targetSq`), so the summed separations are at most
  `11/8 + (11/16)·φ`, where `φ` is the angular spread of the two normals.
- **Lower** — each separation is at least a half-width `h(t) = (1+cos t+sin t)/2`,
  and a chord minorant gives `1 + (7/44)·t ≤ h(t)`, so the sum is at least
  `2 + (7/44)·φ`.

With `φ ≤ π/3 ≤ 22/21`, `chain_gap` shows the lower bound exceeds the upper —
a contradiction. This kills 10 of the 16 patterns.

`Combinatorics.classification` then places the survivor in an explicit list, by
`decide`:

```lean
def remaining : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 3), (1, 1), (1, 2), (3, 2), (3, 3)]
```

### Step 4 — Enumerate the branches

`Combinatorics.lean`

Each separating normal comes from one of the two squares it separates, so
`s e ∈ {first e, last e}`: `2³ = 8` source choices. With the 6 surviving
patterns that is **48 branches**, and the problem is now finite.

### Step 5 — Select a certificate

`select_certificate` (`BranchCover.lean`)

Each of the 48 branches is assigned one of 53 rational certificates, chosen so
its polygon of corners contains the angle pair `x`:

```lean
∃ i : Fin 53, (table i).k = k ∧ (table i).source = s ∧
  targetSq ≤ polynomial (table i) x
```

There are 53 rather than 48 because five branches need their region split:
`AngleDomain.lean` triangulates those, and `cert051` covers a quadrilateral via
two triangles. `table_checked` verifies `arithmeticValid (table i)` for all 53
by `fin_cases i <;> decide +kernel`.

### Step 6 — Lower-bound the polynomial

`certificate_on_hull` (`Concavity.lean`, `RealPolynomial.lean`, `RealBounds.lean`)

This is where rational data becomes a statement about real trigonometry, in
three stages:

- **Corners.** `checked_corner_lower` converts the certificate's rational
  corner checks into real bounds. The bridge is `RealBounds.lean`, which proves
  enclosures for `cos` and `sin` at the six angles `0, π/12, π/8, π/6, π/4, π/3`
  from exact radical identities — no decimals, no series.
- **Concavity.** `polynomial_concave` shows `polynomial c` is concave on the
  domain triangle, by restricting to an arbitrary segment and showing the second
  derivative is `-π²·(g₀u² + g₁v² + g₂(v-u)²) ≤ 0`. Non-negativity of that form
  follows from the certificate's curvature conditions via a `2×2` PSD criterion.
- **Extension.** A concave function on a convex set attains its minimum over a
  polygon at a corner, so the checked corner values extend to the whole hull,
  giving `targetSq ≤ polynomial (table i) x`.

### Step 7 — Upper-bound the same polynomial

`table_dual_bound` (`CoefficientBridge.lean`, `Dual.lean`)

`three_square_dual` is the analytic core: from vertex containment and the
separating inequalities of step 2, completing the square in the weighted sum
yields

```lean
theorem coefficient_identity (i : Fin 53) (x : Point) :
    dualValue (vertices x) (lamReal (table i)) (muReal (table i))
      (widths x) (normal x (table i).k (table i).source) = polynomial (table i) x
```

`coefficient_identity` proves, for each of the 53 records, that the dual value
*equals* `polynomial (table i) x` — a symbolic identity in the rotation angles,
not a numerical comparison. Composing the two gives `table_dual_bound`:

```lean
theorem table_dual_bound (i : Fin 53) (x : Point) (c : Fin 3 → Point) (R : ℝ)
    (hp : Packing (angularSquares c x) (0,0) R)
    (hsep : ∀ e, widths x e ≤ dot
      (normal x (table i).k (table i).source e)
      (sub (c (edgeEnd e)) (c (edgeStart e)))) :
    polynomial (table i) x ≤ R^2
```

### Step 8 — Conclude

`optimality` (`Main.lean`)

Steps 6 and 7 bound the same quantity from opposite sides:

```text
targetSq ≤ polynomial (table i) x ≤ R² < targetSq
```

which is absurd. So `targetSq ≤ R²`, and `radius_lower_of_squared` converts
this to `optimalRadius ≤ R` using `optimalRadius_sq` and `0 ≤ R`.

## Modules

### Geometry and target

| File | Contents |
| --- | --- |
| `Geometry.lean` | Unit squares, disk containment, interior non-overlap, vertex containment |
| `Construction.lean` | The T arrangement: containment, disjointness, attainment |
| `Dual.lean` | Weighted quadratic certificate inequality from vertex containment and separation |
| `Arithmetic.lean` | Centre estimate, rational chain contradiction, 2×2 PSD criterion |

### Reduction to a finite branch

| File | Contents |
| --- | --- |
| `PlaneTools.lean` | Rigid motions, frame reindexing, quarter-turn equivalence |
| `OrientationNormalization.lean` | Arbitrary square frames into the angle triangle |
| `SeparatingAxes.lean` | Separating-axis theorem from a supporting functional |
| `AxisSelection.lean` | Axis transport, first cardinal index normalization |
| `ForbiddenChain.lean` | Exclusion of directed-chain cardinal patterns |
| `Combinatorics.lean` | Enumeration of 16 patterns and 8 source choices to 48 branches |
| `AngleDomain.lean` | Barycentric covers of the angle triangle, quadrilateral triangulation |

### Certificate machinery

| File | Contents |
| --- | --- |
| `RatDefinitions.lean` | `Certificate` structure, `arithmeticValid`, interval tables |
| `Certificates.lean` | 53 rational certificate records |
| `RealBounds.lean` | Real enclosures for `cos`/`sin` at 6 special angles, from exact radicals |
| `RealPolynomial.lean` | Real semantics for the rational certificates |
| `Concavity.lean` | Concavity via second derivative along segments; convex-hull extension |
| `BranchCover.lean` | `table : Fin 53`, `table_checked`, 48-branch selection |
| `CoefficientBridge.lean` | `dualValue = polynomial` for all 53 records; dual bound |
| `Main.lean` | End-to-end assembly |

## Verification

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Requires Elan/Lake and network access for mathlib.

- `lake build` must report zero `declaration uses 'sorry'` warnings.
- Every `#print axioms` line in the audit must read exactly
  `[propext, Classical.choice, Quot.sound]`.
- `sorryAx` in that output would indicate an unproved lemma;
  `Lean.ofReduceBool` would indicate `native_decide` and compiler trust.
- The audit also prints `Packing` and both theorem signatures for inspection.

Build from the committed `lake-manifest.json`, which pins every dependency by
hash. Avoid `lake update`: seven transitive packages track `main` or `master`
and would be re-resolved.

**Trusted base:** Lean, Lake, mathlib. The 53 certificate records are
machine-generated, and each carries a `decide +kernel` proof of
`arithmeticValid` — kernel reduction, so no generator output is trusted.

## License

Apache-2.0, matching mathlib and the Lean ecosystem.

## Contributors

This formalization was produced by two AI models working in sequence.

**ChatGPT 6 Pro** — the mathematics and the initial Lean development. Its
output is preserved verbatim in `reference/`:

- `three_squares_circle_proof.md` — the informal argument
- `three_squares_circle_certificate.py` — a Python verifier
- `three-squares-lean-draft.zip`, `-draft-v2.zip`, `-v3.zip` — three successive
  versions of the Lean development, from first draft to feature-complete. None
  had been run through a compiler.

**Claude Opus 5 High-Max** — compilation and cleanup. Ported the development to
Lean `4.34.0` / mathlib `v4.34.0`, fixed the elaboration, tactic and proof
errors that surfaced once the code was actually run, removed the dead
declarations left by the draft lineage, and arranged the result into this
repository.

Direction, review and the decisions about scope and naming were the
repository owner's.

The Python verifier is a reference artifact and plays no part in the Lean
verification path; every certificate carries its own kernel-checked proof.
