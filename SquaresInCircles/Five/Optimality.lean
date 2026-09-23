import SquaresInCircles.Five.Containing
import SquaresInCircles.Common.Regions
import SquaresInCircles.Five.Construction

/-! Five squares: dodecagon tangents, occupied arcs, and a safe central sweep. -/
noncomputable section
open Set
namespace SquaresInCircles

/-- The only exception to the five-arc contradiction is a square centred at `o`.
Only the closed 12-gon is assumed. -/
lemma five_centered_square (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hp : ∀ i, P5 (alpha (S i) o) (beta (S i) o)) :
    ∃ i, (S i).center=o := by
  by_contra hn
  push Not at hn
  refine ray_budget_impossible (n := 5) (by decide) hd (fun i => (hp i).1) (fun i hi => ?_)
    (fun i hi => by exact_mod_cast five_exterior_arc (S i) o (hp i) hi)
  obtain ⟨A,hA⟩ := five_containing_arc (S i) o hi (hn i)
  exact ⟨A,by rw [hA]; norm_num⟩

/-- The strict tangent relaxation itself is impossible; no circle is assumed here. -/
theorem five_polygon_strict_impossible (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P5Strict (alpha (S i) o) (beta (S i) o)) : False := by
  obtain ⟨k,hk⟩ := five_centered_square S o hd (fun i => p5Strict_to_p5 (hp i))
  obtain ⟨j,hjk⟩ := exists_ne k
  exact center_ne_of_strict_octagon (S k) (S j) o (hd k j hjk.symm) (hp j).1 hk

theorem five_squared_lower (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (5:ℝ)/2 ≤ R^2 := by
  by_contra hn
  exact five_polygon_strict_impossible S o hp.disjoint
    (fun i => p5_of_phi_lt ((hp.phi_le i).trans_lt (lt_of_not_ge hn)))

theorem Five.optimality (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Five.radius ≤ R :=
  le_of_sq_le_sq (by rw [Five.radius_sq]; exact five_squared_lower S o R hp) hp.1

end SquaresInCircles
