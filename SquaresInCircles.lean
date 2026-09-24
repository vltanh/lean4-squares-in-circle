import SquaresInCircles.One.Uniqueness
import SquaresInCircles.Two.Uniqueness
import SquaresInCircles.Three.Uniqueness
import SquaresInCircles.Four.Uniqueness
import SquaresInCircles.Five.Uniqueness
import SquaresInCircles.Seven.Uniqueness

/-!
# Packing one to five, and seven, unit squares in a disk

For `1 ≤ n ≤ 5` and `n = 7`, `optimalRadius n` is the smallest radius of a disk
containing `n` non-overlapping unit squares, and some packing attains it. For
`n ≤ 5` that packing is unique up to a rotation about the disk centre and a
relabelling of the squares. For `n = 7` it is not: the middle column of the
optimal packing can slide, and up to that slide the packing is unique. Each
case can also be imported on its own, from its folder `SquaresInCircles/One/`
to `SquaresInCircles/Seven/`.
-/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for `n` unit squares, `1 ≤ n ≤ 5` or `n = 7`. -/
def optimalRadius : ℕ → ℝ
  | 1 => One.radius
  | 2 => Two.radius
  | 3 => Three.radius
  | 4 => Four.radius
  | 5 => Five.radius
  | 7 => Seven.radius
  | _ => 0

/-- The optimal packings, in the frame of their disk centres. For `n = 7`, the
one with the middle column centred. -/
def modelCenters : (n : ℕ) → Fin n → Point
  | 1 => One.centers
  | 2 => Two.centers
  | 3 => Three.centers
  | 4 => Four.centers
  | 5 => Five.centers
  | 7 => Seven.centers
  | _ => fun _ => (0,0)

theorem optimality (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    optimalRadius n ≤ R := by
  rcases hn with ⟨h1,h5⟩ | rfl
  · interval_cases n
    · exact One.optimality S o R hp
    · exact Two.optimality S o R hp
    · exact Three.optimality S o R hp
    · exact Four.optimality S o R hp
    · exact Five.optimality S o R hp
  · exact Seven.optimality S o R hp

theorem attainment (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5 ∨ n = 7) :
    ∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n) := by
  rcases hn with ⟨h1,h5⟩ | rfl
  · interval_cases n
    · exact One.attainment
    · exact Two.attainment
    · exact Three.attainment
    · exact Four.attainment
    · exact Five.attainment
  · exact Seven.attainment

theorem uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    HasNormalForm S o (modelCenters n) := by
  obtain ⟨h1,h5⟩ := hn
  interval_cases n
  · exact One.uniqueness S o hp
  · exact Two.uniqueness S o hp
  · exact Three.uniqueness S o hp
  · exact Four.uniqueness S o hp
  · exact Five.uniqueness S o hp

/-- For `n = 7`, uniqueness up to the sliding column: every optimal packing
has the normal form of `Seven.slidingCenters c` for some column `c`. -/
theorem sliding_uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o (optimalRadius 7)) :
    ∃ c : Seven.Column, HasNormalForm S o (Seven.slidingCenters c) :=
  Seven.uniqueness S o hp

/-- Uniqueness with the frame replaced by an explicit isometry of the plane that
takes the origin to the disk centre. -/
theorem rigid_uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5)
    (S : Fin n → UnitSquare) (o : Point) (hp : Packing S o (optimalRadius n)) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openAxisSquare (modelCenters n i) p.1 p.2) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedAxisSquare (modelCenters n i) p.1 p.2)) :=
  (uniqueness n hn S o hp).rigid_witness

/-- The optimum for `n ≤ 5` unit squares: lower bound, attainment, uniqueness. -/
theorem optimality_attainment_uniqueness (n : ℕ) (hn : 1 ≤ n ∧ n ≤ 5) :
    (∀ (S : Fin n → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → optimalRadius n ≤ R) ∧
    (∃ (S : Fin n → UnitSquare) (o : Point), Packing S o (optimalRadius n)) ∧
    (∀ (S : Fin n → UnitSquare) (o : Point),
      Packing S o (optimalRadius n) → HasNormalForm S o (modelCenters n)) :=
  ⟨optimality n (Or.inl hn),attainment n (Or.inl hn),uniqueness n hn⟩

end SquaresInCircles
