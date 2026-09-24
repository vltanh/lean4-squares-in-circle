import Mathlib
import SquaresInCircles.Common.Constructions

/-!
# Seven squares: attainment and the complete sliding construction

The original packing predicate is unchanged. The side columns force the
candidate radius, while the three middle squares may slide. This file proves
attainment; it does not use or assert the seven-square lower bound.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Candidate radius. Optimality is a separate theorem. -/
def radius : ℝ := Real.sqrt (13 / 4)

lemma radius_nonneg : 0 ≤ radius := Real.sqrt_nonneg _
lemma radius_sq : radius ^ 2 = 13 / 4 := Real.sq_sqrt (by norm_num)
lemma radius_eq_sqrt_thirteen_half : radius = Real.sqrt 13 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  nlinarith [radius_sq, radius_nonneg]

/-- Largest absolute ordinate of a middle-column center. -/
def columnLimit : ℝ := Real.sqrt 3 - 1 / 2

lemma columnLimit_pos : 0 < columnLimit := by
  dsimp [columnLimit]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

lemma one_le_columnLimit : (1 : ℝ) ≤ columnLimit := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  dsimp [columnLimit]
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

lemma columnLimit_sq : (columnLimit + 1 / 2) ^ 2 = 3 := by
  simp only [columnLimit, sub_add_cancel]
  exact Real.sq_sqrt (by norm_num)

/-- Three ordered centers, including all boundary/sliding contacts. -/
structure Column where
  bottom : ℝ
  middle : ℝ
  top : ℝ
  lower : -columnLimit ≤ bottom
  gap_lower : bottom + 1 ≤ middle
  gap_upper : middle + 1 ≤ top
  upper : top ≤ columnLimit

namespace Column
lemma bottom_le_middle (c : Column) : c.bottom ≤ c.middle := by linarith [c.gap_lower]
lemma middle_le_top (c : Column) : c.middle ≤ c.top := by linarith [c.gap_upper]
lemma bottom_mem (c : Column) : -columnLimit ≤ c.bottom ∧ c.bottom ≤ columnLimit :=
  ⟨c.lower, (c.bottom_le_middle.trans c.middle_le_top).trans c.upper⟩
lemma middle_mem (c : Column) : -columnLimit ≤ c.middle ∧ c.middle ≤ columnLimit :=
  ⟨c.lower.trans c.bottom_le_middle, c.middle_le_top.trans c.upper⟩
lemma top_mem (c : Column) : -columnLimit ≤ c.top ∧ c.top ≤ columnLimit :=
  ⟨(c.lower.trans c.bottom_le_middle).trans c.middle_le_top, c.upper⟩

/-- The four nonnegative slots describe the three-dimensional sliding simplex. -/
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

/-- Recover a sliding column from its four nonnegative slots. -/
def columnOfSlots (g : Fin 4 → ℝ) (hg : ∀ i, 0 ≤ g i)
    (hs : ∑ i, g i = 2 * Real.sqrt 3 - 3) : Column where
  bottom := -columnLimit + g 0
  middle := -columnLimit + g 0 + 1 + g 1
  top := -columnLimit + g 0 + 2 + g 1 + g 2
  lower := by linarith [hg 0]
  gap_lower := by linarith [hg 1]
  gap_upper := by linarith [hg 2]
  upper := by
    have he : g 0 + g 1 + g 2 + g 3 = 2 * Real.sqrt 3 - 3 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hs
    dsimp [columnLimit]
    linarith [hg 3]

/-- The four side centers, then the three movable middle centers. -/
def slidingCenters (c : Column) : Fin 7 → Point :=
  ![(1, -1/2), (1, 1/2), (-1, -1/2), (-1, 1/2),
    (0, c.bottom), (0, c.middle), (0, c.top)]

def slidingModel (c : Column) : Fin 7 → UnitSquare :=
  fun i => axisSquare (slidingCenters c i)

lemma slidingModel_disjoint (c : Column) : InteriorDisjoint (slidingModel c) := by
  have hbm := c.gap_lower
  have hmt := c.gap_upper
  have hbt : c.bottom+1 ≤ c.top := by linarith
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;>
    norm_num [slidingCenters, AxisSeparated, hbm, hmt, hbt] at *

lemma middle_square_contained {y : ℝ} (hy : -columnLimit ≤ y ∧ y ≤ columnLimit) :
    ∀ p, closedSquare (axisSquare (0, y)) p → inDisk (0, 0) radius p := by
  apply axis_contained (B := 1/2) (C := columnLimit + 1/2)
  · norm_num
  · norm_num
  · dsimp; linarith [hy.1]
  · dsimp; linarith [hy.2]
  · rw [columnLimit_sq, radius_sq]
    norm_num

/-- Every point of the sliding simplex is an attaining construction. -/
theorem sliding_packing (c : Column) : Packing (slidingModel c) (0, 0) radius := by
  refine ⟨radius_nonneg, ?_, slidingModel_disjoint c⟩
  intro i
  fin_cases i
  · apply axis_contained (B := 3/2) (C := 1) <;>
      norm_num [slidingModel, slidingCenters, radius_sq]
  · apply axis_contained (B := 3/2) (C := 1) <;>
      norm_num [slidingModel, slidingCenters, radius_sq]
  · apply axis_contained (B := 3/2) (C := 1) <;>
      norm_num [slidingModel, slidingCenters, radius_sq]
  · apply axis_contained (B := 3/2) (C := 1) <;>
      norm_num [slidingModel, slidingCenters, radius_sq]
  · exact middle_square_contained c.bottom_mem
  · exact middle_square_contained c.middle_mem
  · exact middle_square_contained c.top_mem

def centeredColumn : Column where
  bottom := -1
  middle := 0
  top := 1
  lower := by linarith [one_le_columnLimit]
  gap_lower := by norm_num
  gap_upper := by norm_num
  upper := one_le_columnLimit

def centers : Fin 7 → Point := slidingCenters centeredColumn
def model : Fin 7 → UnitSquare := slidingModel centeredColumn

theorem model_packing : Packing model (0, 0) radius := sliding_packing centeredColumn

theorem attainment : ∃ (S : Fin 7 → UnitSquare) (o : Point), Packing S o radius :=
  ⟨model, (0, 0), model_packing⟩

/-- The four side squares already force this radius within the sliding family. -/
theorem sliding_radius_necessary (c : Column) (R : ℝ)
    (hp : Packing (slidingModel c) (0,0) R) : radius ≤ R := by
  have hv : closedSquare (slidingModel c 1) (3/2,1) := by
    norm_num [slidingModel, slidingCenters, axisSquare, closedSquare, localX, localY]
  have hh := hp.2.1 1 (3/2,1) hv
  norm_num [inDisk, normSq, sub] at hh
  nlinarith [radius_sq, radius_nonneg, hp.1]

/-- The middle square contains the disk center, but need not be centered there. -/
lemma sliding_middle_contains (c : Column) : openSquare (slidingModel c 5) (0,0) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hroot : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hlow : -1/2 < c.middle := by
    have hl := c.lower
    dsimp [columnLimit] at hl
    linarith [c.gap_lower]
  have hhigh : c.middle < 1/2 := by
    have hu := c.upper
    dsimp [columnLimit] at hu
    linarith [c.gap_upper]
  norm_num [slidingModel, slidingCenters, axisSquare, openSquare, localX, localY]
  exact abs_lt.mpr ⟨by linarith,hhigh⟩

end SquaresInCircles.Seven
