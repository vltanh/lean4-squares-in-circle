import SquaresInCircles.Seven.Uniqueness.ContactCycle
import SquaresInCircles.Seven.Uniqueness.CommonFrame
import SquaresInCircles.Seven.Uniqueness.Slots

/-!
# Every optimal seven-square packing is in the sliding family

The proof selects the unique origin-containing square, reconstructs the other
six through the equality contact cycle, and uses the side barriers to align the
containing square. The remaining vertical inequalities are exactly `Column`.

No extra contact, orientation, nondegeneracy, or uniqueness hypothesis enters
the theorem. This source draft has not been compiled or kernel audited.
-/
noncomputable section
namespace SquaresInCircles.Seven.Equality

lemma skip_hits_other (j k : Fin 7) (hk : k≠j) :
    ∃ i : Fin 6,skipIndex j i=k := by
  have hneq : k.val≠j.val := by
    intro h
    exact hk (Fin.ext h)
  by_cases hlt : k.val<j.val
  · let i : Fin 6 := ⟨k.val,by omega⟩
    refine ⟨i,Fin.ext ?_⟩
    simp only [skipIndex,i,if_pos hlt]
  · have hgt : j.val<k.val := by omega
    let i : Fin 6 := ⟨k.val-1,by omega⟩
    refine ⟨i,Fin.ext ?_⟩
    have hn : ¬k.val-1<j.val := by omega
    simp only [skipIndex,i,if_neg hn]
    omega

private def wallIndex : Fin 4 → Fin 6 := ![0,1,4,3]

lemma walls_from_ring (top bottom : ℝ) (i : Fin 4) :
    ringCenters top bottom (wallIndex i)=sideCenter i := by
  fin_cases i <;> rfl

private def middleSlot : Fin 6 → Fin 7 := ![0,1,6,3,2,4]

/-- Equality classification without choosing any of the three sliding parameters. -/
theorem classify_optimal (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : SlidingNormalForm S o := by
  classical
  obtain ⟨j,hj⟩ := exists_containing S o hp
  let E := omitEmbedding j
  let U : Fin 6 → UnitSquare := fun i => S (E i)
  have hU : Packing U o radius := packing_reindex hp E
  have hUext (i : Fin 6) : ¬openSquare (U i) o := by
    intro hi
    exact hp.disjoint (E i) j (omit_ne j i) o ⟨hi,hj⟩
  have hUphi (i : Fin 6) : phi (alpha (U i) o) (beta (U i) o)≤targetSq := by
    have hh := hU.phi_le i
    simpa only [radius_sq,targetSq] using hh
  obtain ⟨W⟩ := six_exterior_ring U o hU.disjoint hUext hUphi
  let e : Fin 6 ↪ Fin 7 :=
    ⟨fun i => E (W.order i),by
      intro i k hik
      exact W.order.injective (E.injective hik)⟩
  have he_ne (i : Fin 6) : e i≠j := omit_ne j (W.order i)
  have he_hits (k : Fin 7) (hk : k≠j) : ∃i,e i=k := by
    obtain ⟨i,hi⟩ := skip_hits_other j k hk
    refine ⟨W.order.symm i,?_⟩
    change E (W.order (W.order.symm i))=k
    rw [W.order.apply_symm_apply]
    exact hi
  have hring (i : Fin 6) :
      Represents (S (e i)) o W.phase (ringCenters W.top W.bottom i) := W.represents i
  let B : Fin 4 → UnitSquare := fun i => S (e (wallIndex i))
  have hB (i : Fin 4) : Represents (B i) o W.phase (sideCenter i) := by
    have hh := hring (wallIndex i)
    simpa only [walls_from_ring] using hh
  have hdisj (i : Fin 4) (p : Point) : ¬(openSquare (S j) p∧openSquare (B i) p) := by
    exact hp.disjoint j (e (wallIndex i)) (Ne.symm (he_ne _)) p
  obtain ⟨z,hz,hcentral⟩ := central_represents (S j) B o W.phase hj hB hdisj
  have htop : Represents (S (e 2)) o W.phase (0,W.top) := hring 2
  have hbottom : Represents (S (e 5)) o W.phase (0,-W.bottom) := hring 5
  have hgapTop := aligned_vertical_separation hcentral htop
    (hp.disjoint j (e 2) (Ne.symm (he_ne 2)))
  have hgapBottom := aligned_vertical_separation hbottom hcentral
    (hp.disjoint (e 5) j (he_ne 5))
  have hza := abs_lt.mp hz
  have hsignTop : 0≤W.top-z := by linarith [W.top_bounds.1]
  have hsignBottom : 0≤z-(-W.bottom) := by linarith [W.bottom_bounds.1]
  rw [abs_of_nonneg hsignTop] at hgapTop
  rw [abs_of_nonneg hsignBottom] at hgapBottom
  let c : Column :=
    { bottom := -W.bottom
      middle := z
      top := W.top
      lower := by linarith [W.bottom_bounds.2]
      gap_lower := by linarith
      gap_upper := by linarith
      upper := W.top_bounds.2 }
  refine ⟨c,normal_form_of_slots hp.disjoint ?_⟩
  intro k
  by_cases hk : k=j
  · subst k
    exact ⟨5,hcentral⟩
  · obtain ⟨i,hi⟩ := he_hits k hk
    refine ⟨middleSlot i,?_⟩
    have hh := hring i
    rw [hi] at hh
    have hc : ringCenters W.top W.bottom i=slidingCenters c (middleSlot i) := by
      fin_cases i <;> rfl
    rwa [hc] at hh

end SquaresInCircles.Seven.Equality
