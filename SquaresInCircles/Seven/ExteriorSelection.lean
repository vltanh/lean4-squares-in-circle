import Mathlib
import SquaresInCircles.Common.Basic

/-! Select six exterior squares without changing the original packing model. -/
noncomputable section
namespace SquaresInCircles.Seven

/-- The order-preserving embedding skipping a chosen label. -/
def omit (k : Fin 7) (i : Fin 6) : Fin 7 :=
  ⟨if i.val < k.val then i.val else i.val+1, by
    split_ifs <;> omega⟩

lemma omit_ne (k : Fin 7) (i : Fin 6) : omit k i ≠ k := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [omit] at hv
  split_ifs at hv <;> omega

lemma omit_injective (k : Fin 7) : Function.Injective (omit k) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  dsimp [omit] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

def omitEmbedding (k : Fin 7) : Fin 6 ↪ Fin 7 := ⟨omit k, omit_injective k⟩

lemma packing_reindex {m n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (e : Fin m ↪ Fin n) : Packing (fun i => S (e i)) o R := by
  refine ⟨hp.1, fun i => hp.2.1 (e i), ?_⟩
  intro i j hij p
  exact hp.2.2 (e i) (e j) (fun h => hij (e.injective h)) p

/-- Boundary points count as exterior: only membership in an open square is omitted. -/
theorem six_exterior_indices (S : Fin 7 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) :
    ∃ e : Fin 6 ↪ Fin 7, ∀ i, ¬ openSquare (S (e i)) o := by
  classical
  by_cases h : ∃ k, openSquare (S k) o
  · obtain ⟨k,hk⟩ := h
    refine ⟨omitEmbedding k, ?_⟩
    intro i hi
    exact hd (omit k i) k (omit_ne k i) o ⟨hi,hk⟩
  · refine ⟨omitEmbedding 0, ?_⟩
    intro i hi
    exact h ⟨omit 0 i,hi⟩

end SquaresInCircles.Seven
