import ThreeUnitSquaresInCircle.Unified.Support

noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

/-- At most one region is a ray sweep; all others are the original open squares. -/
def rayRegions {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (i : Fin n) : Set Point :=
  by
    classical
    exact if openSquare (S i) o then openRay (S i) o else {p | openSquare (S i) p}

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
    rw [Set.disjoint_left]
    exact fun p hpi hpj => hd i j hij p ⟨hpi,hpj⟩

end ThreeUnitSquaresInCircle.Unified
