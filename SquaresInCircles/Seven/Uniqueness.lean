import SquaresInCircles.Seven.Optimality
import SquaresInCircles.Seven.Uniqueness.Reconstruction
import SquaresInCircles.Seven.Uniqueness.SevenMarkers
import SquaresInCircles.Seven.Uniqueness.Slots

/-!
# Seven squares: uniqueness up to the sliding column

Every packing of seven unit squares in the disk of radius `√13 / 2` is one of
the sliding packings of `Seven/Construction.lean`, moved by one rotation about
the disk centre and relabelled; the middle column may sit anywhere in its
range. Conversely every such normal form is an optimal packing.

The equality case reruns the lower bound: one square contains the disk centre
(`Uniqueness/SevenMarkers.lean`), the markers of the other six form a regular
hexagon and neighbouring squares touch as in the optimal packing
(`Uniqueness/ContactCycle.lean`), and the square in the middle is pinned
between the side columns (`Uniqueness/CentralSquare.lean`).
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Every packing at the optimal radius is a sliding packing, rotated about the
disk centre and relabelled. -/
theorem uniqueness (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : SlidingNormalForm S o :=
  (Equality.exists_containing S o hp).elim (Equality.normal_form_of_containing S o hp)

/-- Complete classification at the optimum, including the converse. -/
theorem packing_iff_sliding (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔ SlidingNormalForm S o :=
  ⟨uniqueness S o,SlidingNormalForm.packing⟩

/-- The same classification by the four gaps of the column: nonnegative, with
sum `2√3 - 3`. -/
theorem classification_by_slots (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔
    ∃ g : SlotSimplex, HasNormalForm S o (slidingCenters (columnSlotEquiv.symm g)) :=
  (packing_iff_sliding S o).trans columnSlotEquiv.exists_congr_left

end SquaresInCircles.Seven
