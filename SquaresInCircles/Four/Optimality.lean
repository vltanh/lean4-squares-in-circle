import SquaresInCircles.Four.Containing
import SquaresInCircles.Common.Regions
import SquaresInCircles.Four.Construction

/-! Four squares: strict diamond constraints, the circle of radius `1/2`, and
the same disjoint-region angular budget as for five. -/
noncomputable section
open Set
namespace SquaresInCircles

/-- In the closed disk of radius `sqrt 2`, the strict contact diamond is
infeasible: on the circle of radius `1/2` the arcs exceed the budget. -/
theorem four_diamond_impossible (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ 2)
    (hp : ∀ i, P4Strict (alpha (S i) o) (beta (S i) o)) : False := by
  have h8 (i : Fin 4) := p4Strict_to_p8Strict (alpha_nonneg _ _) (beta_nonneg _ _) (hp i)
  choose C hsort using (fun i : Fin 4 => sorted_square_chart (S i) o)
  refine ray_budget_impossible (n := 4) (r := 1/2) (by decide) hd
    (fun i => ⟨(h8 i).1.le,(h8 i).2.le⟩) (fun i hi => ?_) (fun i hi => ?_)
  · obtain ⟨j,hji⟩ := exists_ne i
    have hne := center_ne_of_strict_octagon (S i) (S j) o (hd i j hji.symm) (h8 j)
    obtain ⟨A,hA⟩ := four_containing_arc (r := 1/2) (C i) (hsort i) hi
      ((C i).transfer (fun a b => 0 < a+b) (fun h => by linarith)
        (abs_center_sum_pos (S i) o hne))
      (by norm_num) (by nlinarith [halfDiagonal_sq,halfDiagonal_pos])
    exact ⟨A,by rw [hA]; norm_num⟩
  · obtain ⟨A,-,hA⟩ := four_exterior_arc (C i) (hsort i) hi (chart_phi (C i) (hφ i))
    exact ⟨A,by exact_mod_cast hA ((C i).transfer P4Strict
      (fun h => by dsimp [P4Strict] at *; linarith) (hp i))⟩

theorem four_squared_lower (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (2:ℝ) ≤ R^2 := by
  by_contra hn
  have hlt (i : Fin 4) := (hp.phi_le i).trans_lt (lt_of_not_ge hn)
  exact four_diamond_impossible S o hp.disjoint (fun i => (hlt i).le)
    (fun i => p4_of_phi_lt (hlt i))

theorem Four.optimality (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Four.radius ≤ R :=
  le_of_sq_le_sq (by rw [Four.radius_sq]; exact four_squared_lower S o R hp) hp.1

end SquaresInCircles
