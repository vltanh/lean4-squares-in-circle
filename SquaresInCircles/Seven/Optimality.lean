import SquaresInCircles.Seven.MarkerSeparation

/-!
# Seven squares: unconditional analytical optimality and attainment

The pair theorem is supplied by `marker_separation`, not passed as a packing
hypothesis. The argument uses the original `Packing` predicate throughout.
The construction includes the three-parameter sliding family; no uniqueness
claim or isolated-optimum assumption is made.

This is the completed source draft. It has not been compiled or kernel-audited.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Stronger intermediate theorem: six squares exterior to the specified disk
center require squared radius at least 13/4. -/
theorem six_exterior_squared_lower
    (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hext : ∀i,¬openSquare (S i) o) :
    (13:ℝ)/4≤R^2 :=
  six_exterior_squared_lower_of_marker_separation marker_separation S o R hp hext

theorem six_exterior_lower
    (S : Fin 6 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hext : ∀i,¬openSquare (S i) o) : radius≤R :=
  le_of_sq_le_sq (by rw [radius_sq]; exact six_exterior_squared_lower S o R hp hext) hp.1

/-- No geometric or certificate hypothesis is added to the packing predicate. -/
theorem squared_lower
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (13:ℝ)/4≤R^2 :=
  squared_lower_of_marker_separation marker_separation S o R hp

/-- Proposed unconditional lower-bound endpoint for seven independently rotated
unit squares. Its proof chain uses only lemmas imported above. -/
theorem optimality
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : radius≤R :=
  optimality_of_marker_separation marker_separation S o R hp

theorem optimality_sqrt_thirteen_half
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Real.sqrt 13/2≤R := by
  rw [←radius_eq_sqrt_thirteen_half]
  exact optimality S o R hp

/-- Lower bound and existence of an attaining packing, with no unproved
marker, support, interval-verification or normal-selection assumption. -/
theorem optimality_and_attainment :
    (∀(S : Fin 7 → UnitSquare)(o : Point)(R : ℝ),Packing S o R → radius≤R) ∧
    ∃(S : Fin 7 → UnitSquare)(o : Point),Packing S o radius :=
  ⟨fun S o R hp => optimality S o R hp,attainment⟩

/-- Every allowed slide remains an attaining packing. The lower-bound part is
now the global theorem, not merely the side-corner estimate for the family. -/
theorem sliding_is_optimal (c : Column) :
    Packing (slidingModel c) (0,0) radius ∧
    ∀(S : Fin 7 → UnitSquare)(o : Point)(R : ℝ),Packing S o R → radius≤R :=
  ⟨sliding_packing c,fun S o R hp => optimality S o R hp⟩

end SquaresInCircles.Seven
