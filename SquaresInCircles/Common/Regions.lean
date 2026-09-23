import SquaresInCircles.Common.AngularBudget

/-! The budget for four and five squares: the square that contains the disk
centre is replaced by its radial sweep, and every other square by itself. -/
noncomputable section
open Set
namespace SquaresInCircles

/-- The radial sweep of a square containing `o`, and any other square itself. -/
def rayRegions {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (i : Fin n) : Set Point :=
  by
    classical
    exact if openSquare (S i) o then openRay (S i) o else {p | openSquare (S i) p}

lemma rayRegions_pos {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {i : Fin n}
    (h : openSquare (S i) o) : rayRegions S o i = openRay (S i) o :=
  ite_eq_left h

lemma rayRegions_neg {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {i : Fin n}
    (h : ¬ openSquare (S i) o) : rayRegions S o i = {p | openSquare (S i) p} :=
  ite_eq_right h

lemma rayRegions_disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    (hd : InteriorDisjoint S) (hp : ∀ i, P8 (alpha (S i) o) (beta (S i) o)) :
    Pairwise (fun i j => Disjoint (rayRegions S o i) (rayRegions S o j)) := by
  classical
  intro i j hij
  by_cases hi : openSquare (S i) o <;> by_cases hj : openSquare (S j) o
  · exact False.elim (hd i j hij o ⟨hi,hj⟩)
  · simp only [rayRegions,hi,hj,ite_true,ite_false]
    exact safe_openRay_of_disjoint (S i) (S j) o (hd i j hij) (hp i) (hp j)
  · simp only [rayRegions,hi,hj,ite_true,ite_false]
    exact (safe_openRay_of_disjoint (S j) (S i) o (hd j i hij.symm) (hp j) (hp i)).symm
  · simp only [rayRegions,hi,hj,ite_false]
    exact hd.pairwise hij

/-- `n ≥ 2` disjoint squares with octagon centres cannot all hold arcs of
half-width at least `π/n` in their regions, strictly more for the squares that
do not contain `o`. -/
theorem ray_budget_impossible {n : ℕ} (hn : 2 ≤ n) {S : Fin n → UnitSquare} {o : Point}
    {r : ℝ} (hd : InteriorDisjoint S) (h8 : ∀ i, P8 (alpha (S i) o) (beta (S i) o))
    (hin : ∀ i, openSquare (S i) o →
      ∃ A : OpenArc o r (openRay (S i) o), Real.pi/n ≤ A.halfWidth)
    (hex : ∀ i, ¬ openSquare (S i) o →
      ∃ A : OpenArc o r {p | openSquare (S i) p}, Real.pi/n < A.halfWidth) : False := by
  classical
  have harcs : ∀ i, ∃ A : OpenArc o r (rayRegions S o i), Real.pi/n ≤ A.halfWidth ∧
      (¬ openSquare (S i) o → Real.pi/n < A.halfWidth) := by
    intro i
    by_cases hi : openSquare (S i) o
    · rw [rayRegions_pos hi]
      obtain ⟨A,hA⟩ := hin i hi
      exact ⟨A,hA,fun h => (h hi).elim⟩
    · rw [rayRegions_neg hi]
      obtain ⟨A,hA⟩ := hex i hi
      exact ⟨A,hA.le,fun _ => hA⟩
  choose A hA hstrict using harcs
  obtain ⟨i,hi⟩ : ∃ i, ¬ openSquare (S i) o := by
    by_contra h
    push Not at h
    exact hd ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp [Fin.ext_iff]) o ⟨h _,h _⟩
  exact uniform_arc_excess (by omega) A (rayRegions_disjoint hd h8) hA ⟨i,hstrict i hi⟩

end SquaresInCircles
