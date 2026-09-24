import SquaresInCircles.Seven.Uniqueness.Reconstruction

/-!
# Seven squares: uniqueness up to the sliding column

This is an end-to-end source draft, stacked on the analytical optimality PR.
Neither this development nor that dependency has been compiled or kernel-
audited here. No classification or fixed-contact assumption appears in the
public theorem's hypotheses.

The conclusion is membership in the entire three-dimensional simplex of
middle-column slots, modulo a common Euclidean frame and a permutation. It
is not uniqueness of a single packing, and it does not equate square records.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Every radius-sqrt(13)/2 packing is a rotated, translated and relabeled
member of the full sliding-column family. -/
theorem uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : SlidingNormalForm S o :=
  Equality.classify S o hp

/-- The same geometric classification with an explicit plane isometry. -/
theorem rigid_uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : CongruentToSliding S o :=
  (uniqueness S o hp).rigid

/-- Complete classification at the optimum, including the converse. -/
theorem packing_iff_sliding (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔ SlidingNormalForm S o :=
  ⟨uniqueness S o,SlidingNormalForm.packing⟩

/-- The statement with the radius written as sqrt(13)/2. -/
theorem uniqueness_sqrt_thirteen_half (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o (Real.sqrt 13/2)) : SlidingNormalForm S o := by
  exact uniqueness S o hp

/-- The parameter set is exactly the four nonnegative slots of fixed total;
no equal-spacing, contact, or centered-middle-square constraint is inserted. -/
theorem classification_by_slots (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔
    ∃ g : SlotSimplex, HasNormalForm S o (slidingCenters (columnSlotEquiv.symm g)) := by
  rw [packing_iff_sliding]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨columnSlotEquiv c,?_⟩
    simpa only [Equiv.symm_apply_apply] using hc
  · rintro ⟨g,hg⟩
    exact ⟨columnSlotEquiv.symm g,hg⟩

/-- The lower bound, attainment and equality classification in one interface. -/
theorem optimality_attainment_and_classification :
    (∀ (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ), Packing S o R → radius ≤ R) ∧
    (∀ c : Column, Packing (slidingModel c) (0,0) radius) ∧
    (∀ (S : Fin 7 → UnitSquare) (o : Point),
      Packing S o radius ↔ SlidingNormalForm S o) :=
  ⟨fun S o R hp => optimality S o R hp,sliding_packing,packing_iff_sliding⟩

end SquaresInCircles.Seven
