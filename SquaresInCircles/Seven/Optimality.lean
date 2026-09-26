import SquaresInCircles.Seven.MarkerSeparation
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Seven.ExteriorSelection

/-!
# The seven-square optimum

`Seven.optimality` is the lower bound for arbitrary packings, with every square
rotated independently and an arbitrary disk centre. The sliding packings of
`Seven/Construction.lean` attain it.

In a disk with `R^2 < 13/4`, at most one square contains the disk centre. The
other six have markers pairwise more than `π/3` apart (`marker_separation`),
which six directions cannot be (`six_markers_impossible`).
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Six squares that avoid the disk centre already need `R^2 ≥ 13/4`. -/
theorem six_exterior_squared_lower (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hext : ∀ i, ¬ openSquare (S i) o) : (13:ℝ)/4 ≤ R^2 := by
  by_contra hn
  have hphi (i : Fin 6) : phi (alpha (S i) o) (beta (S i) o) < targetSq :=
    (hp.phi_le i).trans_lt (lt_of_not_ge hn)
  choose C hsort using fun i => sorted_square_chart (S i) o
  exact six_markers_impossible (fun i => chartMarker (C i)) fun i j hij =>
    marker_separation (C i) (C j) (hsort i) (hsort j) (hext i) (hext j) (hphi i) (hphi j)
      (hp.disjoint i j hij)

theorem squared_lower (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (13:ℝ)/4 ≤ R^2 := by
  obtain ⟨e,hext⟩ := six_exterior_indices S o hp.disjoint
  exact six_exterior_squared_lower (fun i => S (e i)) o R (packing_reindex hp e) hext

/-- The geometric lower bound; `Packing` carries no marker, support or separator
assumption. -/
theorem optimality (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius ≤ R :=
  le_of_sq_le_sq (by rw [radius_sq]; exact squared_lower S o R hp) hp.1

end SquaresInCircles.Seven
