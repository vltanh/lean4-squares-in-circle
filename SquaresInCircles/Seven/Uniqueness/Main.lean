import SquaresInCircles.Seven.Uniqueness

/-!
# Convenience entry point for seven-square sliding uniqueness

The primary theorem declarations live in `Seven/Uniqueness.lean`. This module
adds explicit witnesses and convenient aliases; it does not duplicate those
declarations or provide a second competing dependency chain.

This remains an uncompiled source draft depending on the uncompiled n=7
optimality draft. No compilation, axiom audit, or CI operation is reported.
-/
noncomputable section
namespace SquaresInCircles.Seven

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

/-- Alias emphasizing the fixed candidate radius in both directions. -/
theorem packing_at_radius_iff (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔ SlidingNormalForm S o :=
  packing_iff_sliding S o

/-- A radius no greater than the candidate forces both optimality and the
geometric normal form, with no extra equality-contact hypothesis. -/
theorem classification_of_radius_le (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) (hR : R≤radius) :
    R=radius ∧ SlidingNormalForm S o := by
  have he : R=radius := le_antisymm hR (optimality S o R hp)
  refine ⟨he,?_⟩
  rw [he] at hp
  exact uniqueness S o hp

/-- Every optimal packing has four nonnegative slots with the stated sum.
Distinct slot vectors are not asserted to be inequivalent under symmetry. -/
theorem uniqueness_slots (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) :
    ∃ g : SlotSimplex, HasNormalForm S o
      (slidingCenters (columnSlotEquiv.symm g)) :=
  (classification_by_slots S o).mp hp

/-- Every allowed column remains an attaining, classified packing. -/
theorem sliding_classification (c : Column) :
    Packing (slidingModel c) (0,0) radius ∧
    SlidingNormalForm (slidingModel c) (0,0) :=
  ⟨sliding_packing c,slidingModel_normalForm c⟩

/-- The family includes a middle square strictly above the enclosing center. -/
theorem off_center_sliding_attainment :
    ∃ c : Column, 0<c.middle ∧ Packing (slidingModel c) (0,0) radius := by
  let g : Fin 4 → ℝ := ![2*Real.sqrt 3-3,0,0,0]
  have hg (i : Fin 4) : 0≤g i := by
    fin_cases i <;> simp [g] <;> linarith [sliding_slot_budget_pos]
  have hs : ∑ i,g i=2*Real.sqrt 3-3 := by simp [g,Fin.sum_univ_succ]
  let c := columnOfSlots g hg hs
  refine ⟨c,?_,sliding_packing c⟩
  dsimp [c,columnOfSlots,g,columnLimit]
  linarith [sliding_slot_budget_pos]

end SquaresInCircles.Seven
