import ThreeUnitSquaresInCircle.Unified.Cases
import ThreeUnitSquaresInCircle.Unified.Constructions
import ThreeUnitSquaresInCircle.Main

/-!
# The unified endpoint statements

The existing certificate proof is preserved as `three_radius_lower_existing`.
The independent arc route has explicitly draft-labeled endpoints and currently
inherits six admissions from ArcGeometry. No containment or packing definition
has been weakened to carry a desired bound as an assumption.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

/-- Compatibility with the already established theorem, not a new arc proof. -/
theorem three_radius_lower_existing (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : optimalRadius ≤ R :=
  Cert.optimality S o R ((packingN_three_iff S o R).mp hp)

def IsOptimalRadius (n : ℕ) (r : ℝ) : Prop :=
  (∀ (S : Fin n → UnitSquare) (o : Point) (R : ℝ), PackingN S o R → r ≤ R) ∧
  ∃ (S : Fin n → UnitSquare) (o : Point), PackingN S o r

/-- The three exact radius statements. All three use the new arc route here. -/
theorem unified_optimality_draft :
    IsOptimalRadius 3 optimalRadius ∧
    IsOptimalRadius 4 (Real.sqrt 2) ∧
    IsOptimalRadius 5 (Real.sqrt (5/2)) := by
  refine ⟨⟨three_radius_lower_arc_draft, exists_three_packing⟩,
    ⟨four_radius_lower_arc_draft, ?_⟩, ⟨five_radius_lower_arc_draft, ?_⟩⟩
  · exact ⟨blockFour, origin, blockFour_packing⟩
  · exact ⟨plusFive, origin, plusFive_packing⟩

end ThreeUnitSquaresInCircle.Unified
