import ThreeUnitSquaresInCircle.Geometry

/-!
# A finite-family packing interface

This module is additive: it does not change the original three-square definitions.
All squares, disk predicates, and local coordinates are the repository's originals.
The new code is an uncompiled extension draft for Lean/mathlib v4.34.0.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

open scoped BigOperators

abbrev origin : Point := (0, 0)

def Nonoverlapping {ι : Type*} (S : ι → UnitSquare) : Prop :=
  ∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p)

def Contained (S : UnitSquare) (o : Point) (R : ℝ) : Prop :=
  ∀ p, closedSquare S p → inDisk o R p

def PackingN {ι : Type*} (S : ι → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧ (∀ i, Contained (S i) o R) ∧ Nonoverlapping S

@[simp] theorem packingN_three_iff (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ) :
    PackingN S o R ↔ Packing S o R := Iff.rfl

theorem PackingN.reindex {ι κ : Type*} {S : ι → UnitSquare} {o : Point} {R : ℝ}
    (h : PackingN S o R) (f : κ → ι) (hf : Function.Injective f) :
    PackingN (S ∘ f) o R := by
  refine ⟨h.1, fun i => h.2.1 (f i), ?_⟩
  intro i j hij p hp
  exact h.2.2 (f i) (f j) (fun he => hij (hf he)) p hp

theorem at_most_one_containing {ι : Type*} {S : ι → UnitSquare}
    (h : Nonoverlapping S) {i j : ι} {o : Point}
    (hi : openSquare (S i) o) (hj : openSquare (S j) o) : i = j := by
  by_contra hij
  exact h i j hij o ⟨hi, hj⟩

def alpha (S : UnitSquare) (o : Point) : ℝ := |localX S o|
def beta (S : UnitSquare) (o : Point) : ℝ := |localY S o|

def phi (a b : ℝ) : ℝ := (a + 1 / 2) ^ 2 + (b + 1 / 2) ^ 2

theorem alpha_nonneg (S : UnitSquare) (o : Point) : 0 ≤ alpha S o := abs_nonneg _
theorem beta_nonneg (S : UnitSquare) (o : Point) : 0 ≤ beta S o := abs_nonneg _

theorem open_iff_alpha_beta (S : UnitSquare) (o : Point) :
    openSquare S o ↔ alpha S o < 1 / 2 ∧ beta S o < 1 / 2 := Iff.rfl

theorem normSq_local_difference (S : UnitSquare) (p q : Point) :
    normSq (sub p q) =
      (localX S p - localX S q) ^ 2 + (localY S p - localY S q) ^ 2 := by
  calc
    _ = (S.cosine^2 + S.sine^2) * normSq (sub p q) := by rw [S.unit]; ring
    _ = _ := by dsimp [normSq, sub, localX, localY]; ring

/-- Coordinate expression without relying on the product type's supremum norm. -/
theorem normSq_sub_center (S : UnitSquare) (o : Point) :
    normSq (sub S.center o) = alpha S o ^ 2 + beta S o ^ 2 := by
  rw [normSq_local_difference S]
  simp [localX, localY, alpha, beta, sq_abs]

private def farSign (x : ℝ) : ℝ := if x ≤ 0 then 1 / 2 else -(1 / 2)

private theorem farSign_abs (x : ℝ) : |farSign x| = 1 / 2 := by
  unfold farSign
  split_ifs <;> norm_num

private theorem farSign_sq (x : ℝ) :
    (farSign x - x)^2 = (|x| + 1 / 2)^2 := by
  unfold farSign
  split_ifs with hx
  · rw [abs_of_nonpos hx]; ring
  · rw [abs_of_pos (lt_of_not_ge hx)]; ring

/-- The exact farthest-vertex bound, valid for every independently rotated square. -/
theorem phi_le_radius_sq {S : UnitSquare} {o : Point} {R : ℝ}
    (h : Contained S o R) : phi (alpha S o) (beta S o) ≤ R^2 := by
  let q : Point := (farSign (localX S o), farSign (localY S o))
  let p := add S.center (rotate S q)
  have hmem : closedSquare S p := by
    dsimp [p, closedSquare]
    rw [localX_rotated, localY_rotated]
    exact ⟨(farSign_abs _).le, (farSign_abs _).le⟩
  have hp := h p hmem
  change normSq (sub p o) ≤ R^2 at hp
  rw [normSq_local_difference S] at hp
  dsimp [p] at hp
  rw [localX_rotated, localY_rotated] at hp
  simpa only [q, farSign_sq, alpha, beta, phi] using hp

/-- Radius comparison used in the four- and five-square conclusions. -/
theorem sqrt_le_of_sq_le {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R)
    (h : q ≤ R^2) : Real.sqrt q ≤ R := by
  have hs := Real.sq_sqrt hq
  have hn := Real.sqrt_nonneg q
  nlinarith

/-- The converse has no negative-radius ambiguity. -/
theorem radius_sq_lt_of_lt_sqrt {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R)
    (h : R < Real.sqrt q) : R^2 < q := by
  have hs := Real.sq_sqrt hq
  nlinarith

end ThreeUnitSquaresInCircle.Unified
