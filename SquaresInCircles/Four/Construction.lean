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

/-- The block in the frame of its disk centre. -/
def Four.centers : Fin 4 → Point := ![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]

/-- The 2×2 block, centred at the origin. -/
def Four.model : Fin 4 → UnitSquare := fun i => axisSquare (Four.centers i)

lemma Four.model_disjoint : InteriorDisjoint Four.model := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [Four.centers,AxisSeparated] at *

theorem Four.model_packing : Packing Four.model (0,0) Four.radius := by
  refine ⟨Four.radius_nonneg,?_,Four.model_disjoint⟩
  intro i
  fin_cases i <;> apply axis_contained (B := 1) (C := 1) <;>
    norm_num [Four.model,Four.centers,Four.radius_sq]

theorem Four.attainment :
    ∃ (S : Fin 4 → UnitSquare) (o : Point), Packing S o Four.radius :=
  ⟨Four.model,(0,0),Four.model_packing⟩

end SquaresInCircles
