import Mathlib

/-!
# Coordinate definitions for packing unit squares in a disk

The square model allows arbitrary rotations independently for every square.
`openSquare` uses strict local-coordinate inequalities; no separating-axis
condition, certificate, or desired lower bound is built into `Packing`.
-/

noncomputable section
namespace SquaresInCircles

abbrev Point := ℝ × ℝ

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2

def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2

def add (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)
def scale (t : ℝ) (p : Point) : Point := (t * p.1, t * p.2)

lemma normSq_nonneg (p : Point) : 0 ≤ normSq p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma normSq_add (p q : Point) :
    normSq (add p q) = normSq p + 2 * dot p q + normSq q := by
  simp only [normSq, add, dot]
  ring

/-- The columns `(cosine,sine)` and `(-sine,cosine)` form an orthonormal frame. -/
structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1

def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)

def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)

def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2

def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2

/--
Membership in the closed disk of centre `o` and radius `R`, intended for
`0 ≤ R`. The squared form means `inDisk o R p` and `inDisk o (-R) p` agree, so
for negative `R` this is the disk of radius `|R|` rather than an empty set.
Every use here goes through `Packing`, whose first conjunct supplies `0 ≤ R`.
-/
def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2

/-- `n` unit squares packed in the closed disk of centre `o` and radius `R`. -/
def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))

/-- A unit square whose lower-left corner is `(x,y)`. -/
def axisSquare (x y : ℝ) : UnitSquare where
  center := (x + 1 / 2, y + 1 / 2)
  cosine := 1
  sine := 0
  unit := by norm_num

lemma closed_axisSquare_iff (x y : ℝ) (p : Point) :
    closedSquare (axisSquare x y) p ↔
      x ≤ p.1 ∧ p.1 ≤ x + 1 ∧ y ≤ p.2 ∧ p.2 ≤ y + 1 := by
  simp only [closedSquare, localX, localY, axisSquare, one_mul,
    zero_mul, add_zero, neg_zero, zero_add, abs_le]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma open_axisSquare_iff (x y : ℝ) (p : Point) :
    openSquare (axisSquare x y) p ↔
      x < p.1 ∧ p.1 < x + 1 ∧ y < p.2 ∧ p.2 < y + 1 := by
  simp only [openSquare, localX, localY, axisSquare, one_mul,
    zero_mul, add_zero, neg_zero, zero_add, abs_lt]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hx0, hx1, hy0, hy1⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

def rotate (S : UnitSquare) (p : Point) : Point :=
  (S.cosine * p.1 - S.sine * p.2,
   S.sine * p.1 + S.cosine * p.2)

lemma localX_rotated (S : UnitSquare) (p : Point) :
    localX S (add S.center (rotate S p)) = p.1 := by
  calc
    _ = p.1 * (S.cosine ^ 2 + S.sine ^ 2) := by
      simp only [localX, add, rotate]
      ring
    _ = p.1 := by rw [S.unit]; ring

lemma localY_rotated (S : UnitSquare) (p : Point) :
    localY S (add S.center (rotate S p)) = p.2 := by
  calc
    _ = p.2 * (S.cosine ^ 2 + S.sine ^ 2) := by
      simp only [localY, add, rotate]
      ring
    _ = p.2 := by rw [S.unit]; ring

lemma normSq_rotate (S : UnitSquare) (p : Point) :
    normSq (rotate S p) = normSq p := by
  calc
    _ = (S.cosine ^ 2 + S.sine ^ 2) * normSq p := by
      simp only [normSq, rotate]
      ring
    _ = normSq p := by rw [S.unit]; ring

def localVertex : Fin 4 → Point :=
  ![(-1 / 2, -1 / 2), (-1 / 2, 1 / 2), (1 / 2, -1 / 2), (1 / 2, 1 / 2)]

lemma localVertex_normSq (j : Fin 4) : normSq (localVertex j) = 1 / 2 := by
  fin_cases j <;> norm_num [localVertex, normSq]

lemma vertex_mem (S : UnitSquare) (j : Fin 4) :
    closedSquare S (add S.center (rotate S (localVertex j))) := by
  unfold closedSquare
  rw [localX_rotated, localY_rotated]
  fin_cases j <;> norm_num [localVertex]

end SquaresInCircles
