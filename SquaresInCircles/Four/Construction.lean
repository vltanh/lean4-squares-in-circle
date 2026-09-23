import SquaresInCircles.Common.Constructions

/-! The 2×2 block: four unit squares at the optimal radius `sqrt 2`. -/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for four unit squares: half the diagonal of the 2×2 block. -/
def Four.radius : ℝ := Real.sqrt 2

lemma Four.radius_nonneg : 0 ≤ Four.radius := by
  unfold Four.radius
  positivity

lemma Four.radius_sq : Four.radius ^ 2 = 2 := by
  unfold Four.radius
  exact Real.sq_sqrt (by norm_num)

def blockCorners : Fin 4 → Point := ![(-1,-1),(0,-1),(-1,0),(0,0)]
def block : Fin 4 → UnitSquare := fun i => axisSquare (blockCorners i).1 (blockCorners i).2

lemma block_disjoint : InteriorDisjoint block := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [blockCorners,AxisSeparated] at *

lemma block_packing : Packing block (0,0) (Real.sqrt 2) := by
  refine ⟨Real.sqrt_nonneg _,?_,block_disjoint⟩
  intro i
  have hR := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  fin_cases i <;> dsimp [block,blockCorners] <;>
    apply axis_contained (B := 1) (C := 1) <;> norm_num

theorem Four.attainment :
    ∃ (S : Fin 4 → UnitSquare) (o : Point), Packing S o Four.radius :=
  ⟨block,(0,0),block_packing⟩

/-- The block in the frame of its disk centre. -/
def Four.centers : Fin 4 → Point := ![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]

end SquaresInCircles
