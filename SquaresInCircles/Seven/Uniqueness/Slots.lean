import SquaresInCircles.Seven.Construction

/-!
# The column as a simplex

The four gaps of a column, below, between and above its squares, are
nonnegative with sum `2√3 - 3`, and they determine the column: `Column` is
equivalent to that simplex.
-/
noncomputable section
namespace SquaresInCircles.Seven

namespace Column

/-- The four gaps of a column: below it, between its squares, and above it. -/
def slots (c : Column) : Fin 4 → ℝ :=
  ![c.bottom + columnLimit, c.middle - c.bottom - 1,
    c.top - c.middle - 1, columnLimit - c.top]

lemma slots_nonneg (c : Column) (i : Fin 4) : 0 ≤ c.slots i := by
  fin_cases i <;> simp [slots] <;>
    linarith [c.lower, c.gap_lower, c.gap_upper, c.upper]

lemma sum_slots (c : Column) : ∑ i, c.slots i = 2 * Real.sqrt 3 - 3 := by
  simp [slots, Fin.sum_univ_succ, columnLimit]
  ring

end Column

/-- The column with four given nonnegative gaps of total `2√3 - 3`. -/
def columnOfSlots (g : Fin 4 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hs : ∑ i, g i = 2 * Real.sqrt 3 - 3) : Column where
  bottom := -columnLimit + g 0
  middle := -columnLimit + g 0 + 1 + g 1
  top := -columnLimit + g 0 + 2 + g 1 + g 2
  lower := by linarith [hg 0]
  gap_lower := by linarith [hg 1]
  gap_upper := by linarith [hg 2]
  upper := by
    have he := (Fin.sum_univ_four g).symm.trans hs
    dsimp [columnLimit]
    linarith [hg 3]

lemma columnOfSlots_slots (g : Fin 4 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hs : ∑ i, g i = 2 * Real.sqrt 3 - 3) :
    (columnOfSlots g hg hs).slots = g := by
  funext i
  have he := (Fin.sum_univ_four g).symm.trans hs
  fin_cases i <;> dsimp [columnOfSlots, Column.slots, columnLimit] <;> linarith

lemma columnOfSlots_roundtrip (c : Column) :
    columnOfSlots c.slots c.slots_nonneg c.sum_slots = c := by
  cases c
  dsimp [columnOfSlots, Column.slots]
  congr 1 <;> ring

/-- Four nonnegative gaps of total `2√3 - 3`. -/
def SlotSimplex := {g : Fin 4 → ℝ //
  (∀ i, 0 ≤ g i) ∧ ∑ i, g i = 2 * Real.sqrt 3 - 3}

/-- A column is determined by its gaps, and any gaps occur. -/
def columnSlotEquiv : Column ≃ SlotSimplex where
  toFun c := ⟨c.slots,c.slots_nonneg,c.sum_slots⟩
  invFun g := columnOfSlots g.1 g.2.1 g.2.2
  left_inv c := columnOfSlots_roundtrip c
  right_inv g := Subtype.ext (columnOfSlots_slots g.1 g.2.1 g.2.2)

end SquaresInCircles.Seven
