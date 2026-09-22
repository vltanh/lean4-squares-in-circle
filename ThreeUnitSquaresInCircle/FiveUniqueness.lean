import ThreeUnitSquaresInCircle.Uniqueness.Five

noncomputable section
namespace ThreeUnitSquaresInCircle.FiveUniqueness
open Unified Uniqueness

theorem uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hp : PackingN S o (Real.sqrt ((5:ℝ)/2))) : HasNormalForm S o fiveCenters :=
  five_uniqueness S o hp

/-- Stronger than circular uniqueness: the closed dodecagon is already rigid. -/
theorem polygon_uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P5 (alpha (S i) o) (beta (S i) o)) :
    HasNormalForm S o fiveCenters := five_polygon_uniqueness S o hd hp

theorem rigid_uniqueness (S : Fin 5 → UnitSquare) (o : Point)
    (hp : PackingN S o (Real.sqrt ((5:ℝ)/2))) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin 5)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, closedSquare (S (σ i)) (e p) ↔ ClosedRect (fiveCenters i) p.1 p.2) :=
  (uniqueness S o hp).rigid_witness

end ThreeUnitSquaresInCircle.FiveUniqueness
