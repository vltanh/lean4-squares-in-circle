import SquaresInCircles.Common.Constructions

/-! The 2 × 1 rectangle centred at the disk centre, at the optimal radius `sqrt 5 / 2`. -/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for two unit squares: half the diagonal of the 2 × 1 rectangle. -/
def Two.radius : ℝ := Real.sqrt 5 / 2

lemma Two.radius_nonneg : 0 ≤ Two.radius := by
  unfold Two.radius
  positivity

lemma Two.radius_sq : Two.radius ^ 2 = 5 / 4 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold Two.radius
  nlinarith

def Two.corners : Fin 2 → Point := ![(-1,-1/2),(0,-1/2)]

/-- The 2 × 1 rectangle, centred at the origin. -/
def Two.model : Fin 2 → UnitSquare :=
  fun i => axisSquare (Two.corners i).1 (Two.corners i).2

lemma Two.model_disjoint : InteriorDisjoint Two.model := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [Two.corners,AxisSeparated] at *

theorem Two.model_packing : Packing Two.model (0,0) Two.radius := by
  refine ⟨Two.radius_nonneg,?_,Two.model_disjoint⟩
  intro i
  have hR := Two.radius_sq
  fin_cases i <;> dsimp [Two.model,Two.corners] <;>
    apply axis_contained (B := 1) (C := 1/2) <;> norm_num [hR]

theorem Two.attainment :
    ∃ (S : Fin 2 → UnitSquare) (o : Point), Packing S o Two.radius :=
  ⟨Two.model,(0,0),Two.model_packing⟩

/-- The rectangle in the frame of its disk centre. -/
def Two.centers : Fin 2 → Point := ![(-1/2,0),(1/2,0)]

end SquaresInCircles
