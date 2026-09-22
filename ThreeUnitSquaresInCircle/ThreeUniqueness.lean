import ThreeUnitSquaresInCircle.Uniqueness.Three

noncomputable section
namespace ThreeUnitSquaresInCircle.ThreeUniqueness
open Unified Uniqueness

/-- Uniqueness of square sets up to one rotation/translation and relabeling. -/
theorem uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o optimalRadius) : HasNormalForm S o threeCenters :=
  three_uniqueness S o hp

theorem rigid_uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o optimalRadius) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin 3)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, closedSquare (S (σ i)) (e p) ↔ ClosedRect (threeCenters i) p.1 p.2) :=
  (uniqueness S o hp).rigid_witness

end ThreeUnitSquaresInCircle.ThreeUniqueness
