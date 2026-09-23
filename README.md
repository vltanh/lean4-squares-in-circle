# Formalization of "Squares in Circles" in Lean 4

[![Lean build](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/lean.yml/badge.svg)](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/lean.yml)
[![Doc links](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/docs.yml/badge.svg)](https://github.com/vltanh/lean4-squares-in-circles/actions/workflows/docs.yml)

Machine-checked proofs, for `n = 1, …, 5`, of the smallest radius of a disk
that holds `n` non-overlapping unit squares, and that exactly one packing
attains it, up to rotation about the disk centre and relabelling of the squares.

| n | optimal radius | ≈ | the unique optimal packing |
| :-: | :-: | :-: | :-: |
| 1 | `√2 / 2` | 0.7071 | <img src="https://erich-friedman.github.io/packing/squincir/1.gif" width="100" alt="one unit square in a circle"><br>the square |
| 2 | `√5 / 2` | 1.1180 | <img src="https://erich-friedman.github.io/packing/squincir/2.gif" width="100" alt="two unit squares in a circle"><br>a 2×1 rectangle |
| 3 | `5√17 / 16` | 1.2885 | <img src="https://erich-friedman.github.io/packing/squincir/3.gif" width="100" alt="three unit squares in a circle"><br>the T |
| 4 | `√2` | 1.4142 | <img src="https://erich-friedman.github.io/packing/squincir/4.gif" width="100" alt="four unit squares in a circle"><br>the 2×2 block |
| 5 | `√(5/2)` | 1.5811 | <img src="https://erich-friedman.github.io/packing/squincir/5.gif" width="100" alt="five unit squares in a circle"><br>the plus |

Pictures by Erich Friedman, from the [Squares in Circles](https://erich-friedman.github.io/packing/squincir/)
page of Erich's Packing Center.

## Definitions

More on each definition: [docs/definitions.md](docs/definitions.md).

Read the definitions before trusting the results. A kernel check establishes
that the proofs are valid; it cannot establish that the statements mean what
you intend.

### Squares

A point is a pair of reals, and a unit square is a centre with an orthonormal
frame `(cosine, sine)`, so every square is placed and rotated independently
(`SquaresInCircles/Geometry.lean`):

```lean
abbrev Point := ℝ × ℝ

structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1
```

`localX S p` and `localY S p` are the coordinates of `p` in the frame of `S`.
In those coordinates the square is `[-1/2, 1/2]²`, closed or open:

```lean
def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)

def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)

def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2

def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2
```

### Packing

A packing of `n` squares in the closed disk of centre `o` and radius `R` asks
only that every closed square lie in the disk and that no point be interior to
two squares. The disk is described with the squared length `normSq`:

```lean
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)

def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2

def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))
```

### Uniqueness

Uniqueness says that every packing at the optimal radius is the optimal packing
of the table, moved by one rotation about the disk centre, with the squares
relabelled. It compares point sets, not frames, since a quarter turn of a frame
describes the same square. `pointInDirection o φ x y` is the point with
coordinates `(x, y)` in the frame at `o` rotated by the angle `φ` (a
`Direction`, that is, a `Real.Angle`). `OpenRect c` and `ClosedRect c` are the
axis-parallel unit square centred at `c`. These are in `Geometry.lean` too:

```lean
def pointInDirection (o : Point) (phase : Direction) (x y : ℝ) : Point :=
  (o.1 + phase.cos * x - phase.sin * y, o.2 + phase.sin * x + phase.cos * y)

abbrev OpenRect (c : Point) (x y : ℝ) : Prop :=
  |x - c.1| < 1 / 2 ∧ |y - c.2| < 1 / 2
abbrev ClosedRect (c : Point) (x y : ℝ) : Prop :=
  |x - c.1| ≤ 1 / 2 ∧ |y - c.2| ≤ 1 / 2

def HasNormalForm {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    (centers : Fin n → Point) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i x y,
    (openSquare (S (σ i)) (pointInDirection o φ x y) ↔ OpenRect (centers i) x y) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ x y) ↔ ClosedRect (centers i) x y)
```

## Results

More on each theorem: [docs/results.md](docs/results.md).

For `1 ≤ n ≤ 5`, the root file `SquaresInCircles.lean` proves, in namespace
`SquaresInCircles`:

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

`optimalRadius n` is the optimal radius, and `modelCenters n` lists the centres
of the optimal packing, with its disk centre at the origin. Their definitions
in Lean are:

| n | `optimalRadius n` | `modelCenters n` |
| :-: | --- | --- |
| 1 | `Real.sqrt 2 / 2` | `![(0,0)]` |
| 2 | `Real.sqrt 5 / 2` | `![(-1/2,0),(1/2,0)]` |
| 3 | `5 * Real.sqrt 17 / 16` | `![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]` |
| 4 | `Real.sqrt 2` | `![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]` |
| 5 | `Real.sqrt (5 / 2)` | `![(0,0),(1,0),(0,1),(-1,0),(0,-1)]` |

Each case also stands alone, in namespaces `One` to `Five`, with the same
three theorems. `rigid_uniqueness` restates uniqueness with an explicit
isometry of the plane.

## Proof outline

The proofs as mathematics: the setting first, then the shared toolkit, then
one page per case: [docs/proof/](docs/proof/README.md)
([preliminaries](docs/proof/preliminaries.md),
[shared lemmas](docs/proof/common.md), [one](docs/proof/one.md),
[two](docs/proof/two.md), [three](docs/proof/three.md),
[four](docs/proof/four.md), [five](docs/proof/five.md)).

- **One and two squares.** The farthest corner of a square is at least half a
  diagonal from the disk centre. For two squares, the centres of disjoint unit
  squares are at least 1 apart, and the parallelogram law does the rest.
- **Three to five squares.** A smaller disk puts every square's centre strictly
  inside a contact polygon. Each square then occupies an arc of a small circle
  around the disk centre, and together the arcs would need more than the whole
  circle. A square containing the disk centre needs a separate argument, which
  for three squares is the hardest part of the proof.
- **Uniqueness.** With equality allowed, every inequality in the chain must be
  tight, and the tight cases are reconstructed exactly.

## Prior work

More on each earlier result, with references:
[docs/prior-work.md](docs/prior-work.md).

- **One and two squares** are folklore; Erich Friedman's page lists them as
  trivial.
- **Three squares.** Montanher, Neumaier, Markót, Domes and Schichl (2019)
  enclosed the optimal radius in an interval of width `6·10⁻¹⁴` containing
  `5√17/16`, and every optimal arrangement in small boxes near the T, by a
  computer-assisted interval branch-and-bound search. The enclosure trusts
  C++ code and interval rounding, and gives neither the exact radius nor exact
  uniqueness.
- **Four squares** are reported on Friedman's page as proved at the
  International Math Summer Camp in 2026; we found no publication.
- **Five squares.** We found no earlier proof; the plus is listed only as the
  best known packing.

We found no proof-assistant verification of any optimal square or circle
packing. Here every case is proved exactly, uniqueness included, and checked by
Lean's kernel.

## Layout

More on each file: [docs/layout.md](docs/layout.md).

```text
SquaresInCircles.lean      optimalRadius, and all five cases in one statement
SquaresInCircles/
├── Geometry.lean          the statement: squares, disks, Packing, normal forms
├── Common/                tools shared by several cases
├── One/  Two/             Construction, Optimality, Uniqueness
└── Three/ Four/ Five/     Construction, Tangents, Exterior, Containing,
                           Optimality, Uniqueness
```

No case imports another.

## Verification

More on each check: [docs/verification.md](docs/verification.md).

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
lake env lean SanityChecks.lean
```

The build uses Lean `4.34.0` and mathlib `v4.34.0`, pinned by `lean-toolchain`
and `lake-manifest.json`. `lake build` must report no `sorry`, and every
`#print axioms` line must read exactly `[propext, Classical.choice, Quot.sound]`.
The trusted base is Lean, Lake and mathlib. On every push, GitHub Actions runs
the build, audits the axioms of every declaration, and runs both check files;
the badge at the top shows the result. A second workflow, with its own badge,
checks that the links from the proof pages to the Lean declarations are
current.

## License

Apache-2.0, matching mathlib and the Lean ecosystem.

## Contributors

The proofs and the Lean code were written by AI models, ChatGPT 6 Pro and
Claude Opus 5 and 5.5, with the repository owner directing and reviewing the
work. Who did what, and when: [docs/contributors.md](docs/contributors.md).
