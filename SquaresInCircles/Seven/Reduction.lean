import SquaresInCircles.Seven.Construction
import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Seven.ExteriorSelection

/-!
# Exact proof boundary for the seven-square lower bound

The assembly from marker separation to the original packing statement is
proved here. `MarkerSeparationStatement` is NOT asserted: proving it for
arbitrary independently rotated squares is the unfinished geometric task.
No statement below is an unconditional seven-square lower bound.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- The actual pair theorem still needed, with concrete chart markers and the
original square membership predicates. This is neither `True` nor a condition
silently inserted into `Packing`. -/
def MarkerSeparationStatement : Prop :=
  ∀ (S T : UnitSquare) (o : Point) (C : SquareChart S o) (D : SquareChart T o),
    C.b ≤ C.a → D.b ≤ D.a →
    (¬ openSquare S o) → (¬ openSquare T o) →
    phi (alpha S o) (beta S o) < targetSq →
    phi (alpha T o) (beta T o) < targetSq →
    (∀ p, ¬ (openSquare S p ∧ openSquare T p)) →
    gap < dist (chartMarker C) (chartMarker D)

/-- With the pair theorem supplied, six strictly contained exterior squares
are impossible. No cyclic sorting lemma or extra angular hypothesis is needed. -/
theorem six_exterior_impossible_of_marker_separation
    (hpair : MarkerSeparationStatement)
    (S : Fin 6 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hext : ∀ i, ¬ openSquare (S i) o)
    (hphi : ∀ i, phi (alpha (S i) o) (beta (S i) o) < targetSq) : False := by
  classical
  choose C hsort using (fun i : Fin 6 => sorted_square_chart (S i) o)
  apply six_markers_impossible (fun i => chartMarker (C i))
  intro i j hij
  have h := hpair (S i) (S j) o (C i) (C j) (hsort i) (hsort j)
    (hext i) (hext j) (hphi i) (hphi j) (hd i j hij)
  exact h

/-- Conditional on the unproved marker-pair theorem, the stronger exterior
six-square lower bound follows for the unchanged packing predicate. -/
theorem six_exterior_squared_lower_of_marker_separation
    (hpair : MarkerSeparationStatement)
    (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hext : ∀ i, ¬ openSquare (S i) o) : targetSq ≤ R^2 := by
  by_contra hn
  exact six_exterior_impossible_of_marker_separation hpair S o hp.disjoint hext
    (fun i => (hp.phi_le i).trans_lt (lt_of_not_ge hn))

theorem squared_lower_of_marker_separation
    (hpair : MarkerSeparationStatement)
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : targetSq ≤ R^2 := by
  obtain ⟨e,hext⟩ := six_exterior_indices S o hp.disjoint
  exact six_exterior_squared_lower_of_marker_separation hpair
    (fun i => S (e i)) o R (packing_reindex hp e) hext

theorem optimality_of_marker_separation
    (hpair : MarkerSeparationStatement)
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius ≤ R := by
  have hsq := squared_lower_of_marker_separation hpair S o R hp
  change (13 : ℝ)/4 ≤ R^2 at hsq
  nlinarith [radius_sq, radius_nonneg, hp.1]

/-- This theorem still has the displayed substantive hypothesis `hpair`.
The unconditional component is only the attaining construction. -/
theorem optimality_and_attainment_of_marker_separation
    (hpair : MarkerSeparationStatement) :
    (∀ (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → radius ≤ R) ∧
    ∃ (S : Fin 7 → UnitSquare) (o : Point), Packing S o radius :=
  ⟨fun S o R hp => optimality_of_marker_separation hpair S o R hp, attainment⟩

end SquaresInCircles.Seven
