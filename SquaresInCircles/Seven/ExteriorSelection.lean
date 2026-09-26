import SquaresInCircles.Common.Basic

/-!
# Six exterior squares

A subfamily of a packing is a packing. Of seven squares with disjoint
interiors at most one contains the disk centre in its interior, so six of them
avoid it.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma packing_reindex {m n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (e : Fin m ↪ Fin n) : Packing (fun i => S (e i)) o R :=
  ⟨hp.1,fun i => hp.2.1 (e i),fun i j hij => hp.2.2 (e i) (e j) (e.injective.ne hij)⟩

/-- Boundary points count as exterior: only membership in an open square is omitted. -/
theorem six_exterior_indices (S : Fin 7 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) :
    ∃ e : Fin 6 ↪ Fin 7, ∀ i, ¬ openSquare (S (e i)) o := by
  by_cases h : ∃ k, openSquare (S k) o
  · obtain ⟨k,hk⟩ := h
    exact ⟨k.succAboveEmb,fun i hi => hd _ k (k.succAbove_ne i) o ⟨hi,hk⟩⟩
  · exact ⟨Fin.succAboveEmb 0,fun i hi => h ⟨_,hi⟩⟩

end SquaresInCircles.Seven
