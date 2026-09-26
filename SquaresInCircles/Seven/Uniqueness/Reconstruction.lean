import SquaresInCircles.Seven.Uniqueness.ContactCycle
import SquaresInCircles.Seven.Uniqueness.SevenMarkers
import SquaresInCircles.Seven.Uniqueness.CentralSquare
import SquaresInCircles.Seven.Uniqueness.Slots
import SquaresInCircles.Seven.ExteriorSelection

/-!
# Reconstruction

The ring of six squares and the square in the middle, in one frame, with the
heights of the middle column at least 1 apart: the sliding normal form.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

lemma central_outer_cover (k : Fin 7) (e : Fin 6 ↪ Fin 7)
    (hne : ∀ i, e i ≠ k) : ∀ j, j = k ∨ ∃ i, e i = j := by
  let f : Fin 7 → Fin 7 := Fin.cases k (fun i => e i)
  have hf : Function.Injective f := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        rfl
      · intro he
        exact False.elim (hne j (by simpa [f] using he.symm))
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro he
        exact False.elim (hne i (by simpa [f] using he))
      · intro he
        exact congrArg Fin.succ (e.injective (by simpa [f] using he))
  have hsurj := Finite.surjective_of_injective hf
  intro j
  obtain ⟨i,hi⟩ := hsurj j
  refine Fin.cases ?_ (fun i => ?_) i hi
  · intro he
    exact Or.inl (by simpa [f] using he.symm)
  · intro he
    exact Or.inr ⟨i,by simpa [f] using he⟩

/-- Two aligned squares in one column cannot have centers less than one apart. -/
lemma column_centers_separated {S T : UnitSquare} {o : Point} {φ : Direction} {x y : ℝ}
    (hS : Represents S o φ (0,x)) (hT : Represents T o φ (0,y))
    (hxy : x ≤ y) (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) : x+1 ≤ y := by
  by_contra hn
  have hlt : y-x < 1 := by linarith
  let m := (x+y)/2
  have hx : openAxisSquare (0,x) 0 m := by
    dsimp [openAxisSquare,m]
    constructor
    · norm_num
    · apply abs_lt.mpr
      constructor <;> linarith
  have hy : openAxisSquare (0,y) 0 m := by
    dsimp [openAxisSquare,m]
    constructor
    · norm_num
    · apply abs_lt.mpr
      constructor <;> linarith
  exact hd (pointInDirection o φ 0 m) ⟨(hS 0 m).mpr hx,(hT 0 m).mpr hy⟩

def sideRingIndex : Fin 4 → Fin 6 := ![0,1,4,3]
def outerSlot : Fin 6 → Fin 7 := ![0,1,6,3,2,4]

lemma ring_sides (top bottom : ℝ) (i : Fin 4) :
    ringCenters top bottom (sideRingIndex i) = sideCenters i := by
  fin_cases i <;> rfl

lemma ring_column_slots (c : Column) (i : Fin 6) :
    ringCenters c.top (-c.bottom) i = slidingCenters c (outerSlot i) := by
  fin_cases i <;> simp [ringCenters,slidingCenters,outerSlot]

/-- An optimal packing in which square `k` contains the disk centre has the
sliding normal form. -/
theorem normal_form_of_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) (k : Fin 7) (hk : openSquare (S k) o) :
    SlidingNormalForm S o := by
  classical
  let f : Fin 6 ↪ Fin 7 := omitEmbedding k
  have hfk (i : Fin 6) : f i ≠ k := omit_ne k i
  have hext (i : Fin 6) : ¬ openSquare (S (f i)) o := by
    intro hi
    exact hp.disjoint (f i) k (hfk i) o ⟨hi,hk⟩
  have hpack := packing_reindex hp f
  have hphi (i : Fin 6) : phi (alpha (S (f i)) o) (beta (S (f i)) o) ≤ targetSq := by
    have hh := hp.phi_le (f i)
    simpa only [radius_sq,targetSq] using hh
  obtain ⟨W⟩ := six_exterior_ring (fun i => S (f i)) o hpack.disjoint hext hphi
  let e : Fin 6 ↪ Fin 7 :=
    { toFun := fun i => f (W.order i)
      inj' := fun i j hij => W.order.injective (f.injective hij) }
  have hek (i : Fin 6) : e i ≠ k := hfk (W.order i)
  have hrep (i : Fin 6) : Represents (S (e i)) o W.phase (ringCenters W.top W.bottom i) :=
    W.represents i
  let B : Fin 4 → UnitSquare := fun i => S (e (sideRingIndex i))
  have hb (i : Fin 4) : Represents (B i) o W.phase (sideCenters i) := by
    simpa only [B,ring_sides] using hrep (sideRingIndex i)
  have hdisj (i : Fin 4) (p : Point) : ¬ (openSquare (B i) p ∧ openSquare (S k) p) :=
    hp.disjoint _ k (hek (sideRingIndex i)) p
  obtain ⟨z,hz,hcenter⟩ := central_square_represents hk hb hdisj
  have ht : Represents (S (e 2)) o W.phase (0,W.top) := by
    simpa only [ringCenters,Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons] using hrep 2
  have hbot : Represents (S (e 5)) o W.phase (0,-W.bottom) := by
    simpa [ringCenters] using hrep 5
  have hza := abs_lt.mp hz
  have htopgap : z+1 ≤ W.top := column_centers_separated hcenter ht
    (by linarith [W.top_bounds.1])
    (hp.disjoint k (e 2) (Ne.symm (hek 2)))
  have hbottomgap : -W.bottom+1 ≤ z := column_centers_separated hbot hcenter
    (by linarith [W.bottom_bounds.1])
    (hp.disjoint (e 5) k (hek 5))
  let c : Column :=
    { bottom := -W.bottom
      middle := z
      top := W.top
      lower := by linarith [W.bottom_bounds.2]
      gap_lower := hbottomgap
      gap_upper := htopgap
      upper := W.top_bounds.2 }
  refine ⟨c,?_⟩
  apply normal_form_of_slots (φ := W.phase) hp.disjoint
  intro j
  rcases central_outer_cover k e hek j with rfl | ⟨i,hi⟩
  · refine ⟨5,?_⟩
    simpa [slidingCenters,c] using hcenter
  · refine ⟨outerSlot i,?_⟩
    have hr := hrep i
    rw [hi] at hr
    have hslot : ringCenters W.top W.bottom i = slidingCenters c (outerSlot i) := by
      have hh := ring_column_slots c i
      simpa [c] using hh
    simpa only [hslot] using hr

/-- Every optimal seven-square packing belongs to the sliding family. -/
theorem classify (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : SlidingNormalForm S o := by
  obtain ⟨k,hk⟩ := exists_containing S o hp
  exact normal_form_of_containing S o hp k hk

end Equality
end SquaresInCircles.Seven
