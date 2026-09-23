import SquaresInCircles.Three.Containing
import SquaresInCircles.Three.Construction

/-!
# The three-square optimum by occupied arcs

`Three.optimality` is the lower bound for arbitrary packings, with every square
rotated independently and an arbitrary disk centre. The T of
`Three/Construction.lean` attains it.

A packing with `R^2 < 425/256` puts every square's centre strictly inside the
contact 16-gon (`p3_of_phi_lt`). `three_polygon_strict_impossible` refutes that
polygon relaxation, for whichever square contains the disk centre, by the
exterior case (`Three/Exterior.lean`) and the containing case
(`Three/Containing.lean`).
-/
noncomputable section
namespace SquaresInCircles

/-- The strict contact 16-gon is infeasible, whichever square contains `o`. -/
theorem three_polygon_strict_impossible (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) : False := by
  obtain ⟨i,hi⟩ := three_exterior_reduction S o hd hp
  exact three_containing_impossible S o hd i hi (hp i) fun j => p3Strict_to_p3 (hp j)

theorem Three.squared_lower (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (425:ℝ)/256 ≤ R^2 := by
  by_contra hn
  have hsmall : R^2 < (425:ℝ)/256 := lt_of_not_ge hn
  exact three_polygon_strict_impossible S o hp.disjoint
    (fun i => p3_of_phi_lt ((hp.phi_le i).trans_lt hsmall))

/-- The geometric lower bound; `Packing` carries no arc, tangent, or separator
assumption. -/
theorem Three.optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Three.radius ≤ R :=
  le_of_sq_le_sq (by rw [Three.radius_sq]; exact Three.squared_lower S o R hp) hp.1

end SquaresInCircles
