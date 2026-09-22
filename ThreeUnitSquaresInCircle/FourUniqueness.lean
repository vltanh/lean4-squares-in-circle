import ThreeUnitSquaresInCircle.Uniqueness.Four

noncomputable section
namespace ThreeUnitSquaresInCircle.FourUniqueness
open Unified Uniqueness

theorem uniqueness (S : Fin 4 → UnitSquare) (o : Point)
    (hp : PackingN S o (Real.sqrt 2)) : HasNormalForm S o fourCenters :=
  four_uniqueness S o hp

theorem rigid_uniqueness (S : Fin 4 → UnitSquare) (o : Point)
    (hp : PackingN S o (Real.sqrt 2)) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin 4)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, closedSquare (S (σ i)) (e p) ↔ ClosedRect (fourCenters i) p.1 p.2) :=
  (uniqueness S o hp).rigid_witness

end ThreeUnitSquaresInCircle.FourUniqueness
