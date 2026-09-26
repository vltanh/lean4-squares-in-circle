import SquaresInCircles.Seven.Uniqueness.ContactCycle
import SquaresInCircles.Seven.Uniqueness.CentralSquare
import SquaresInCircles.Seven.Uniqueness.NormalForm

/-!
# Reconstruction

The ring of six squares and the square in the middle, in one frame, with the
heights of the middle column at least 1 apart: the sliding normal form.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

/-- Two aligned squares in one column cannot have centers less than one apart. -/
lemma column_centers_separated {S T : UnitSquare} {o : Point} {φ : Direction} {x y : ℝ}
    (hS : Represents S o φ (0,x)) (hT : Represents T o φ (0,y))
    (hxy : x ≤ y) (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) : x+1 ≤ y := by
  by_contra hn
  refine hd (pointInDirection o φ 0 ((x+y)/2)) ⟨(hS _ _).mpr ?_,(hT _ _).mpr ?_⟩ <;>
    exact ⟨by norm_num,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

def sideRingIndex : Fin 4 → Fin 6 := ![0,1,4,3]
def outerSlot : Fin 6 → Fin 7 := ![0,1,6,3,2,4]

/-- An optimal packing in which square `k` contains the disk centre has the
sliding normal form. -/
theorem normal_form_of_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) (k : Fin 7) (hk : openSquare (S k) o) :
    SlidingNormalForm S o := by
  obtain ⟨W⟩ := six_exterior_ring (fun i => S (k.succAbove i)) o
    (fun i j hij => hp.disjoint _ _ (Fin.succAbove_right_injective.ne hij))
    (fun i hi => hp.disjoint _ k (k.succAbove_ne i) o ⟨hi,hk⟩)
    (fun i => by simpa only [radius_sq,targetSq] using hp.phi_le (k.succAbove i))
  obtain ⟨z,hz,hcenter⟩ := central_square_represents
    (B := fun i => S (k.succAbove (W.order (sideRingIndex i)))) hk
    (fun i => by fin_cases i <;> exact W.represents _) (fun i => hp.disjoint _ k (k.succAbove_ne _))
  have htop : z+1 ≤ W.top := column_centers_separated hcenter (W.represents 2)
    (by linarith [W.top_bounds.1,abs_lt.mp hz]) (hp.disjoint k _ (k.succAbove_ne _).symm)
  have hbottom : -W.bottom+1 ≤ z := column_centers_separated (W.represents 5) hcenter
    (by linarith [W.bottom_bounds.1,abs_lt.mp hz]) (hp.disjoint _ k (k.succAbove_ne _))
  let c : Column :=
    { bottom := -W.bottom
      middle := z
      top := W.top
      lower := by linarith [W.bottom_bounds.2]
      gap_lower := hbottom
      gap_upper := htop
      upper := W.top_bounds.2 }
  refine ⟨c,normal_form_of_slots (φ := W.phase) hp.disjoint fun j => ?_⟩
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i,rfl⟩
  · exact ⟨5,by simpa [slidingCenters,c] using hcenter⟩
  obtain ⟨l,rfl⟩ := W.order.surjective i
  have hslot : ringCenters W.top W.bottom l = slidingCenters c (outerSlot l) := by
    fin_cases l <;> simp [ringCenters,slidingCenters,outerSlot,c]
  exact ⟨outerSlot l,hslot ▸ W.represents l⟩

end Equality
end SquaresInCircles.Seven
