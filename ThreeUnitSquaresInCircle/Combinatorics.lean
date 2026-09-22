import Mathlib

/-!
The complete finite enumeration of cardinal patterns.
This does not prove the geometric assertion that a chain is impossible.
The proof uses kernel reduction (`decide`), not `native_decide`.
Status: compiles against Lean 4.34.0 / mathlib v4.34.0.
-/
namespace ThreeUnitSquaresInCircle.Combinatorics

def direction (k02 k12 : Fin 4) (i j : Fin 3) : Fin 4 :=
  if i = 0 ∧ j = 1 then 0
  else if i = 1 ∧ j = 0 then 2
  else if i = 0 ∧ j = 2 then k02
  else if i = 2 ∧ j = 0 then k02 + 2
  else if i = 1 ∧ j = 2 then k12
  else if i = 2 ∧ j = 1 then k12 + 2
  else 0

def hasChain (k02 k12 : Fin 4) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    direction k02 k12 i j = direction k02 k12 j k

instance (k02 k12 : Fin 4) : Decidable (hasChain k02 k12) :=
  inferInstanceAs (Decidable (∃ i j k : Fin 3, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
    direction k02 k12 i j = direction k02 k12 j k))

def remaining : List (Fin 4 × Fin 4) :=
  [(0, 1), (0, 3), (1, 1), (1, 2), (3, 2), (3, 3)]

set_option maxRecDepth 100000 in
/-- All sixteen patterns, including all six directed paths for each pattern. -/
theorem classification :
    ∀ k02 k12 : Fin 4, ¬ hasChain k02 k12 ↔ (k02, k12) ∈ remaining := by
  decide

theorem remaining_length : remaining.length = 6 := by decide

def sources : List (Fin 3 × Fin 3 × Fin 3) :=
  [(0, 0, 1), (0, 0, 2), (0, 2, 1), (0, 2, 2),
   (1, 0, 1), (1, 0, 2), (1, 2, 1), (1, 2, 2)]

theorem source_classification :
    ∀ s0 s1 s2 : Fin 3,
      (s0 = 0 ∨ s0 = 1) ∧ (s1 = 0 ∨ s1 = 2) ∧ (s2 = 1 ∨ s2 = 2) ↔
      (s0, s1, s2) ∈ sources := by decide

theorem branch_count : remaining.length * sources.length = 48 := by decide

end ThreeUnitSquaresInCircle.Combinatorics
