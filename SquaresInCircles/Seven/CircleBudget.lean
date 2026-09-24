import Mathlib
import SquaresInCircles.Common.AngularBudget

/-!
# Six separated markers cannot fit on the angular circle

This is a metric/measure theorem, independent of square geometry. It uses the
repository's proved `closed_arc_budget`, avoiding cyclic sorting and any
assumption that markers are themselves occupied-arc midpoints.
-/
noncomputable section
open scoped BigOperators
open Set
namespace SquaresInCircles.Seven

private lemma common_strict_lower {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (L : ℝ) (hf : ∀ i ∈ s, L < f i) :
    ∃ r : ℝ, L < r ∧ ∀ i ∈ s, r < f i := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      exact ⟨L+1, by linarith, by simp⟩
  | @insert i s hi ih =>
      intro hf
      obtain ⟨r,hr,hrf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hmin : L < min r (f i) :=
        lt_min hr (hf i (Finset.mem_insert_self _ _))
      obtain ⟨r',hL,hu⟩ := exists_between hmin
      refine ⟨r',hL,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hu.trans_le (min_le_right _ _)
      · exact (hu.trans_le (min_le_left _ _)).trans (hrf j hj)

/-- Six points cannot all have pairwise circular distances strictly above pi/3. -/
theorem six_markers_impossible (c : Fin 6 → Direction)
    (hsep : Pairwise (fun i j => Real.pi/3 < dist (c i) (c j))) : False := by
  classical
  let b : (Fin 6 × Fin 6) → ℝ := fun p =>
    if p.1 = p.2 then Real.pi/2 else dist (c p.1) (c p.2)/2
  have hb (p : Fin 6 × Fin 6) : Real.pi/6 < b p := by
    dsimp [b]
    split_ifs with h
    · linarith [Real.pi_pos]
    · linarith [hsep h]
  obtain ⟨r,hr,hrb⟩ := common_strict_lower Finset.univ b (Real.pi/6)
    (fun p _ => hb p)
  have hrpi : r < Real.pi/2 := by
    have hh := hrb (0,0) (Finset.mem_univ _)
    simpa only [b, ite_eq_left rfl] using hh
  have hnonneg : 0 ≤ r := by linarith [Real.pi_pos]
  have hballs : Pairwise (fun i j =>
      Disjoint (Metric.closedBall (c i) r) (Metric.closedBall (c j) r)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    have hi' : dist z (c i) ≤ r := hi
    have hj' : dist z (c j) ≤ r := hj
    have hdist : dist (c i) (c j) ≤ 2*r := by
      calc
        _ ≤ dist (c i) z + dist z (c j) := dist_triangle _ _ _
        _ ≤ r+r := add_le_add (by simpa [dist_comm] using hi') hj'
        _ = _ := by ring
    have hh := hrb (i,j) (Finset.mem_univ _)
    have hh' : r < dist (c i) (c j)/2 := by
      simpa only [b, ite_eq_right hij] using hh
    linarith
  have hbudget := closed_arc_budget (n := 6) c (fun _ => r)
    (fun _ => ⟨hnonneg, by linarith [Real.pi_pos]⟩) hballs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hbudget
  norm_num at hbudget
  linarith

/-- Pigeonhole form of the same lemma. -/
theorem six_markers_close (c : Fin 6 → Direction) :
    ∃ i j, i ≠ j ∧ dist (c i) (c j) ≤ Real.pi/3 := by
  classical
  by_contra h
  apply six_markers_impossible c
  intro i j hij
  by_contra hd
  exact h ⟨i,j,hij,le_of_not_gt hd⟩

end SquaresInCircles.Seven
