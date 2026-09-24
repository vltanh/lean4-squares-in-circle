import SquaresInCircles.Seven.Uniqueness.NormalForm

/-!
# The sliding column really is the full closed simplex

These identities preserve the bottom, two internal, and top slots. In
particular the middle square is not constrained to be centered at the disk
center, and the top and bottom squares need not touch the circle.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma columnOfSlots_slots (g : Fin 4 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hs : ∑ i, g i = 2 * Real.sqrt 3 - 3) :
    (columnOfSlots g hg hs).slots = g := by
  funext i
  have he : g 0 + g 1 + g 2 + g 3 = 2 * Real.sqrt 3 - 3 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs
  fin_cases i <;> dsimp [columnOfSlots, Column.slots, columnLimit] <;> linarith

lemma columnOfSlots_roundtrip (c : Column) :
    columnOfSlots c.slots c.slots_nonneg c.sum_slots = c := by
  cases c
  congr <;> dsimp [columnOfSlots, Column.slots] <;> ring

lemma column_slots_injective : Function.Injective Column.slots := by
  intro c d he
  have hb := congrFun he (0 : Fin 4)
  have hm := congrFun he (1 : Fin 4)
  have ht := congrFun he (2 : Fin 4)
  have hbottom : c.bottom = d.bottom := by dsimp [Column.slots] at hb; linarith
  have hmiddle : c.middle = d.middle := by dsimp [Column.slots] at hm; linarith
  have htop : c.top = d.top := by dsimp [Column.slots] at ht; linarith
  cases c
  cases d
  simp_all

/-- No implicit equality of the four slots is part of the family. -/
def SlotSimplex := {g : Fin 4 → ℝ //
  (∀ i, 0 ≤ g i) ∧ ∑ i, g i = 2 * Real.sqrt 3 - 3}

def columnSlotEquiv : Column ≃ SlotSimplex where
  toFun c := ⟨c.slots,c.slots_nonneg,c.sum_slots⟩
  invFun g := columnOfSlots g.1 g.2.1 g.2.2
  left_inv c := columnOfSlots_roundtrip c
  right_inv g := Subtype.ext (columnOfSlots_slots g.1 g.2.1 g.2.2)

/-- Every simplex point produces an attaining packing. -/
theorem slots_attainment (g : SlotSimplex) :
    ∃ c : Column, c.slots = g.1 ∧ Packing (slidingModel c) (0,0) radius :=
  ⟨columnSlotEquiv.symm g,
    columnOfSlots_slots g.1 g.2.1 g.2.2, sliding_packing _⟩

lemma column_middle_strict_bounds (c : Column) :
    -(Real.sqrt 3-3/2) ≤ c.middle ∧ c.middle ≤ Real.sqrt 3-3/2 := by
  have hlo := c.lower
  have hhi := c.upper
  dsimp [columnLimit] at hlo hhi
  exact ⟨by linarith [c.gap_lower],by linarith [c.gap_upper]⟩

lemma column_middle_abs_lt_quarter (c : Column) : |c.middle| < 1/4 := by
  have hb := column_middle_strict_bounds c
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr : Real.sqrt 3 < 7/4 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  exact abs_lt.mpr ⟨by linarith [hb.1],by linarith [hb.2]⟩

end SquaresInCircles.Seven
