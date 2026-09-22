import ThreeUnitSquaresInCircle.Unified.ThreeContaining
import ThreeUnitSquaresInCircle.Construction

/-!
# The three-square optimum by occupied arcs

`optimality` is the lower bound for arbitrary packings, with every square
rotated independently and an arbitrary disk centre. `optimality_and_attainment`
adds the T arrangement of `Construction.lean`, which attains it.

A packing with `R^2 < 425/256` puts every square's centre strictly inside the
contact 16-gon (`p3_of_phi_lt`), and `Unified.three_polygon_strict_impossible`
refutes that polygon relaxation. This module does not import the four-square,
five-square, or combined endpoints.
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

/-- The geometric lower bound; `Packing` carries no arc, tangent, or separator
assumption. -/
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
