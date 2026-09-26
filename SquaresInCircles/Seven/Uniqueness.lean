import SquaresInCircles.Seven.Uniqueness.Reconstruction
import SquaresInCircles.Seven.Optimality

/-!
# Seven squares: uniqueness up to the sliding column

Every packing of seven unit squares in the disk of radius `√13 / 2` is one of
the sliding packings of `Seven/Construction.lean`, moved by one rotation about
the disk centre and relabelled; the middle column may sit anywhere in its
range. Conversely every such normal form is an optimal packing.

The equality case reruns the lower bound: the markers of the six squares that
avoid the disk centre form a regular hexagon (`Uniqueness/Hexagon.lean`),
neighbouring squares touch as in the optimal packing
(`Uniqueness/ContactCycle.lean`), and the square in the middle is pinned
between the side columns (`Uniqueness/CentralSquare.lean`).
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Every packing at the optimal radius is a sliding packing, rotated about the
disk centre and relabelled. -/
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

/-- The same classification by the four gaps of the column: nonnegative, with
sum `2√3 - 3`. -/
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

end SquaresInCircles.Seven
