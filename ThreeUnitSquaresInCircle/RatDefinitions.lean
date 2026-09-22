import ThreeUnitSquaresInCircle.Combinatorics

/-!
# Executable rational certificate definitions

`arithmeticValid` is purely rational. In particular, the intervals below
are data: this module does not assert that they enclose real sin/cos values.
Connecting these definitions to the real-valued `dualValue` also requires a
rotation/coefficient identity. Neither fact is assumed as an axiom.
Status: compiles against Lean 4.34.0 / mathlib v4.34.0.
-/
open scoped BigOperators
namespace ThreeUnitSquaresInCircle.RatData

abbrev RPoint := ℚ × ℚ

def rdot (p q : RPoint) : ℚ := p.1 * q.1 + p.2 * q.2
def rcross (p q : RPoint) : ℚ := p.1 * q.2 - p.2 * q.1

def verts : Fin 4 → RPoint :=
  ![(-1/2, -1/2), (-1/2, 1/2), (1/2, -1/2), (1/2, 1/2)]
def dirs : Fin 4 → RPoint := ![(1,0), (0,1), (-1,0), (0,-1)]
def first : Fin 3 → Fin 3 := ![0,0,1]
def last : Fin 3 → Fin 3 := ![1,2,2]

inductive Corner where
  | O | V | W | P | Z
  deriving DecidableEq, Repr

inductive Angle where
  | zero | a15 | a22_5 | a30 | a45 | a60
  deriving DecidableEq, Repr

def cornerAngles : Corner → Fin 3 → Angle
  | .O => ![.zero, .zero, .zero]
  | .V => ![.zero, .a45, .a45]
  | .W => ![.a30, .a60, .a30]
  | .P => ![.zero, .a22_5, .a22_5]
  | .Z => ![.a15, .a30, .a15]

/-- Rational enclosures supplied as data, not as assumptions about sine/cosine. -/
def cosInterval : Angle → ℚ × ℚ
  | .zero => (1,1)
  | .a15 => (965925/1000000,965926/1000000)
  | .a22_5 => (923879/1000000,923880/1000000)
  | .a30 => (866025/1000000,866026/1000000)
  | .a45 => (707106/1000000,707107/1000000)
  | .a60 => (499999/1000000,500001/1000000)

def sinInterval : Angle → ℚ × ℚ
  | .zero => (0,0)
  | .a15 => (258819/1000000,258820/1000000)
  | .a22_5 => (382683/1000000,382684/1000000)
  | .a30 => (499999/1000000,500001/1000000)
  | .a45 => (707106/1000000,707107/1000000)
  | .a60 => (866025/1000000,866026/1000000)

structure Certificate where
  isBase : Bool
  k : Fin 3 → Fin 4
  source : Fin 3 → Fin 3
  lam : Fin 3 → Fin 4 → ℚ
  mu : Fin 3 → ℚ
  coeff : Fin 7 → ℚ
  corners : List Corner

def weight (c : Certificate) (i : Fin 3) : ℚ := ∑ j, c.lam i j

def vectorTable (c : Certificate) (i p : Fin 3) : RPoint :=
  let m : RPoint :=
    if i = p then (∑ j, c.lam i j * (verts j).1, ∑ j, c.lam i j * (verts j).2)
    else (0,0)
  let f (e : Fin 3) : ℚ :=
    if c.source e = p then
      ((if i = first e then 1 else 0) - (if i = last e then 1 else 0)) * c.mu e / 2
    else 0
  (m.1 + ∑ e, f e * (dirs (c.k e)).1,
   m.2 + ∑ e, f e * (dirs (c.k e)).2)

def calculatedC (c : Certificate) : ℚ :=
  1/2 + (∑ e, c.mu e)/2 -
    ∑ i, ∑ p, rdot (vectorTable c i p) (vectorTable c i p) / weight c i

def calculatedA (c : Certificate) (e : Fin 3) : ℚ :=
  c.mu e / 2 - ∑ i,
    2 * rdot (vectorTable c i (first e)) (vectorTable c i (last e)) / weight c i

def calculatedB (c : Certificate) (e : Fin 3) : ℚ :=
  c.mu e / 2 + ∑ i,
    2 * rcross (vectorTable c i (first e)) (vectorTable c i (last e)) / weight c i

def calculatedCoefficients (c : Certificate) : Fin 7 → ℚ :=
  ![calculatedC c, calculatedA c 0, calculatedA c 1, calculatedA c 2,
    calculatedB c 0, calculatedB c 1, calculatedB c 2]

def A (c : Certificate) : Fin 3 → ℚ := ![c.coeff 1,c.coeff 2,c.coeff 3]
def B (c : Certificate) : Fin 3 → ℚ := ![c.coeff 4,c.coeff 5,c.coeff 6]

def curvatureLower (c : Certificate) (e : Fin 3) : ℚ :=
  A c e * (if 0 ≤ A c e then (![6/7,1/2,7/10] : Fin 3 → ℚ) e else 1) +
  min (B c e) 0 * (![1/2,7/8,3/4] : Fin 3 → ℚ) e

def termLower (q : ℚ) (I : ℚ × ℚ) : ℚ :=
  if 0 ≤ q then q * I.1 else q * I.2

def valueLower (c : Certificate) (p : Corner) : ℚ :=
  c.coeff 0 + ∑ e,
    (termLower (A c e) (cosInterval (cornerAngles p e)) +
     termLower (B c e) (sinInterval (cornerAngles p e)))

def cornerOK (c : Certificate) (p : Corner) : Prop :=
  if p = .O then c.isBase = true ∧ valueLower c p = 425/256
  else 425/256 + 1/250 < valueLower c p

instance (c : Certificate) (p : Corner) : Decidable (cornerOK c p) := by
  unfold cornerOK
  infer_instance

def arithmeticValid (c : Certificate) : Prop :=
  c.k 0 = 0 ∧
  (∀ e, c.source e = first e ∨ c.source e = last e) ∧
  (∀ i j, 0 ≤ c.lam i j) ∧
  (∑ i, ∑ j, c.lam i j) = 1 ∧
  (∀ i, 0 < weight c i) ∧
  (∀ e, 0 ≤ c.mu e) ∧
  (∀ j, c.coeff j = calculatedCoefficients c j) ∧
  1/3 < curvatureLower c 0 + curvatureLower c 2 ∧
  3/16 < curvatureLower c 1 + curvatureLower c 2 ∧
  3/40 < curvatureLower c 0 * curvatureLower c 1 +
      curvatureLower c 0 * curvatureLower c 2 +
      curvatureLower c 1 * curvatureLower c 2 ∧
  c.corners.all (fun p => decide (cornerOK c p)) = true

instance (c : Certificate) : Decidable (arithmeticValid c) := by
  unfold arithmeticValid
  infer_instance

end ThreeUnitSquaresInCircle.RatData
