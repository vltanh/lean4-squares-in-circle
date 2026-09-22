import ThreeUnitSquaresInCircle.Unified.ThreeContaining
import ThreeUnitSquaresInCircle.Construction

/-!
# Standalone three-square optimum by occupied arcs

This entry point does not import `ThreeUnitSquaresInCircle.Main`, nor the
four-square, five-square, or combined optimum entry points. The lower bound
uses strict contact-polygon infeasibility, including the containing-square
case, and never calls `Cert.optimality`.

Status: explicit, uncompiled proof scripts. No Lean/Lake/CI execution was
performed while preparing this change. This header is not an axiom-audit result.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.ThreeArc
open Unified

theorem squared_lower (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (425:ℝ)/256 ≤ R^2 := by
  by_contra hn
  have hsmall : R^2 < (425:ℝ)/256 := lt_of_not_ge hn
  have hN : PackingN S o R := hp
  exact three_polygon_strict_impossible S o hN.disjoint
    (fun i => p3_of_phi_lt ((hN.phi_le i).trans_lt hsmall))

/-- The ordinary geometric lower bound, with no certificate-existence assumption. -/
theorem optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius ≤ R := by
  apply radius_lower_of_squared hp.1
  exact squared_lower S o R hp

theorem optimality_and_attainment :
    (∀ (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → optimalRadius ≤ R) ∧
    ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o optimalRadius :=
  ⟨optimality,exists_packing_at_optimum⟩

end ThreeUnitSquaresInCircle.ThreeArc
