import SquaresInCircles.Seven.Uniqueness.Classification

/-!
# Seven-square uniqueness up to the sliding column

Every optimal packing is congruent to a member of `Column`. This is not
uniqueness of an individual packing and does not fix any of the four slots.
The underlying object is the geometric square set, not its frame record.

These are end-to-end proposed proof scripts, not a report of Lean acceptance.
No compilation or CI work has been performed for this extension.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Classification under the original packing assumptions only. -/
theorem uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : SlidingNormalForm S o :=
  Equality.classify_optimal S o hp

/-- Explicit frame-and-permutation version of the classification. -/
theorem uniqueness_column (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) :
    ∃ (c : Column) (φ : Direction) (σ : Equiv.Perm (Fin 7)),
      ∀ i x y,
        (openSquare (S (σ i)) (pointInDirection o φ x y) ↔
          OpenRect (slidingCenters c i) x y) ∧
        (closedSquare (S (σ i)) (pointInDirection o φ x y) ↔
          ClosedRect (slidingCenters c i) x y) :=
  uniqueness S o hp

/-- The equivalence sends the canonical enclosing center to the supplied one
and preserves Euclidean squared distances. It identifies open and closed sets. -/
theorem rigid_uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : CongruentToSliding S o :=
  (uniqueness S o hp).rigid

/-- Both directions: exactly the allowed sliding columns attain this radius. -/
theorem packing_at_radius_iff (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔ SlidingNormalForm S o :=
  ⟨uniqueness S o,fun h => h.packing⟩

/-- A radius no greater than the candidate forces both optimality and the
geometric normal form. There is no additional equality-contact hypothesis. -/
theorem classification_of_radius_le (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hR : R≤radius) :
    R=radius ∧ SlidingNormalForm S o := by
  have he : R=radius := le_antisymm hR (optimality S o R hp)
  refine ⟨he,?_⟩
  rw [he] at hp
  exact uniqueness S o hp

/-- Canonical parameterization by the four slots, with one affine constraint.
This does not claim that distinct slot vectors are inequivalent under symmetry. -/
theorem uniqueness_slots (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) :
    ∃ g : SlotSimplex, HasNormalForm S o
      (slidingCenters (columnSlotEquiv.symm g)) := by
  obtain ⟨c,hc⟩ := uniqueness S o hp
  refine ⟨columnSlotEquiv c,?_⟩
  simpa only [Equiv.symm_apply_apply] using hc

/-- The three-parameter freedom is preserved, not quotiented to one arrangement. -/
theorem sliding_classification (c : Column) :
    Packing (slidingModel c) (0,0) radius ∧
    SlidingNormalForm (slidingModel c) (0,0) :=
  ⟨sliding_packing c,slidingModel_normalForm c⟩

end SquaresInCircles.Seven
