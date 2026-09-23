import SquaresInCircles.Common.Constructions

/-! The plus: five unit squares at the optimal radius `sqrt (5/2)`. -/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for five unit squares: the distance from the disk centre
to the outer corners of the plus. -/
def Five.radius : ℝ := Real.sqrt (5 / 2)

lemma Five.radius_nonneg : 0 ≤ Five.radius := by
  unfold Five.radius
  positivity

lemma Five.radius_sq : Five.radius ^ 2 = 5 / 2 := by
  unfold Five.radius
  exact Real.sq_sqrt (by norm_num)

/-- The plus in the frame of its disk centre. -/
def Five.centers : Fin 5 → Point := ![(0,0),(1,0),(0,1),(-1,0),(0,-1)]

/-- The plus, centred at the origin. -/
def Five.model : Fin 5 → UnitSquare := fun i => axisSquare (Five.centers i)

lemma Five.model_disjoint : InteriorDisjoint Five.model := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [Five.centers,AxisSeparated] at *

theorem Five.model_packing : Packing Five.model (0,0) Five.radius := by
  refine ⟨Five.radius_nonneg,?_,Five.model_disjoint⟩
  intro i
  fin_cases i <;>
    first
    | (apply axis_contained (B := 1/2) (C := 3/2) <;>
        norm_num [Five.model,Five.centers,Five.radius_sq]; done)
    | (apply axis_contained (B := 3/2) (C := 1/2) <;>
        norm_num [Five.model,Five.centers,Five.radius_sq])

theorem Five.attainment :
    ∃ (S : Fin 5 → UnitSquare) (o : Point), Packing S o Five.radius :=
  ⟨Five.model,(0,0),Five.model_packing⟩

end SquaresInCircles
