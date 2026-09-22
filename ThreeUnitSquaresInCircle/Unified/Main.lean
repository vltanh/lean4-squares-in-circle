import ThreeUnitSquaresInCircle.Main
import ThreeUnitSquaresInCircle.Unified.Four
import ThreeUnitSquaresInCircle.Unified.Five
import ThreeUnitSquaresInCircle.Unified.Constructions
import ThreeUnitSquaresInCircle.Unified.ThreeExterior

/-!
# Shared interface for three, four and five unit squares

Status: uncompiled extension draft, targeting the repository's pinned Lean and
mathlib versions.  The three-square endpoint below deliberately reuses the
existing compiled certificate theorem; it is NOT claimed to have been replaced
by an independent arc proof.  The four- and five-square endpoints have proposed
end-to-end arc proof bodies in this extension.  See `docs/UNIFIED_ARCS.md`.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

/-- Preserve the checked three-square theorem through a definitionally identical API. -/
theorem three_optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : optimalRadius ≤ R :=
  Cert.optimality S o R hp

def candidateRadius (n : ℕ) : ℝ :=
  if n=3 then optimalRadius else if n=4 then Real.sqrt 2 else
    if n=5 then Real.sqrt ((5:ℝ)/2) else 0

/-- Common geometric statement; no arc, tangent, separator, or certificate
assumption is inserted into `PackingN`. -/
theorem optimality_345 (n : ℕ) (hn : n=3 ∨ n=4 ∨ n=5)
    (S : Fin n → UnitSquare) (o : Point) (R : ℝ) (hp : PackingN S o R) :
    candidateRadius n ≤ R := by
  rcases hn with rfl | rfl | rfl
  · simpa [candidateRadius] using three_optimality S o R hp
  · simpa [candidateRadius] using four_optimality S o R hp
  · simpa [candidateRadius] using five_optimality S o R hp

theorem attainment_345 (n : ℕ) (hn : n=3 ∨ n=4 ∨ n=5) :
    ∃ (S : Fin n → UnitSquare) (o : Point), PackingN S o (candidateRadius n) := by
  rcases hn with rfl | rfl | rfl
  · obtain ⟨S,o,hp⟩ := ThreeUnitSquaresInCircle.exists_packing_at_optimum
    exact ⟨S,o,by simpa [candidateRadius] using hp⟩
  · exact ⟨block,(0,0),by simpa [candidateRadius] using block_packing⟩
  · exact ⟨plus,(0,0),by simpa [candidateRadius] using plus_packing⟩

theorem optimality_and_attainment_345 (n : ℕ) (hn : n=3 ∨ n=4 ∨ n=5) :
    (∀ (S : Fin n → UnitSquare) (o : Point) (R : ℝ),
      PackingN S o R → candidateRadius n ≤ R) ∧
    ∃ (S : Fin n → UnitSquare) (o : Point), PackingN S o (candidateRadius n) :=
  ⟨fun S o R hp => optimality_345 n hn S o R hp,attainment_345 n hn⟩

end ThreeUnitSquaresInCircle.Unified
