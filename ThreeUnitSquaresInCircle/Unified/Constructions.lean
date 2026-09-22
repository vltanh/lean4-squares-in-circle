import ThreeUnitSquaresInCircle.Unified.Basic
import ThreeUnitSquaresInCircle.Construction

/-! # Attaining configurations; no arc-geometry admissions are imported here. -/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

def blockFour : Fin 4 → UnitSquare :=
  ![axisSquare (-1) (-1), axisSquare 0 (-1), axisSquare (-1) 0, axisSquare 0 0]

def plusFive : Fin 5 → UnitSquare :=
  ![axisSquare (-1/2) (-1/2), axisSquare (1/2) (-1/2),
    axisSquare (-3/2) (-1/2), axisSquare (-1/2) (1/2), axisSquare (-1/2) (-3/2)]

lemma blockFour_packing : PackingN blockFour origin (Real.sqrt 2) := by
  refine ⟨by positivity, ?_, ?_⟩
  · intro i p hp
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    fin_cases i <;> norm_num [blockFour, closed_axisSquare_iff] at hp <;>
      rcases hp with ⟨hxl,hxu,hyl,hyu⟩ <;>
      have hx := mul_nonneg (sub_nonneg.mpr hxl) (sub_nonneg.mpr hxu) <;>
      have hy := mul_nonneg (sub_nonneg.mpr hyl) (sub_nonneg.mpr hyu) <;>
      dsimp [inDisk, sub, normSq, origin] <;> nlinarith
  · intro i j hij p hp
    fin_cases i <;> fin_cases j <;>
      norm_num [blockFour, open_axisSquare_iff] at hij hp <;>
      rcases hp with ⟨⟨hxl,hxu,hyl,hyu⟩,⟨hxl',hxu',hyl',hyu'⟩⟩ <;> linarith

lemma plusFive_packing : PackingN plusFive origin (Real.sqrt (5/2)) := by
  refine ⟨by positivity, ?_, ?_⟩
  · intro i p hp
    have hs : (Real.sqrt (5/2))^2 = (5/2 : ℝ) := Real.sq_sqrt (by norm_num)
    fin_cases i <;> norm_num [plusFive, closed_axisSquare_iff] at hp <;>
      rcases hp with ⟨hxl,hxu,hyl,hyu⟩ <;>
      have hx := mul_nonneg (sub_nonneg.mpr hxl) (sub_nonneg.mpr hxu) <;>
      have hy := mul_nonneg (sub_nonneg.mpr hyl) (sub_nonneg.mpr hyu) <;>
      dsimp [inDisk, sub, normSq, origin] <;> nlinarith
  · intro i j hij p hp
    fin_cases i <;> fin_cases j <;>
      norm_num [plusFive, open_axisSquare_iff] at hij hp <;>
      rcases hp with ⟨⟨hxl,hxu,hyl,hyu⟩,⟨hxl',hxu',hyl',hyu'⟩⟩ <;> linarith

lemma exists_three_packing : ∃ (S : Fin 3 → UnitSquare) (o : Point),
    PackingN S o optimalRadius := by
  simpa only [packingN_three_iff] using ThreeUnitSquaresInCircle.exists_packing_at_optimum

end ThreeUnitSquaresInCircle.Unified
