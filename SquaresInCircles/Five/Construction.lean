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

def plusCorners : Fin 5 → Point :=
  ![(-1/2,-1/2),(1/2,-1/2),(-3/2,-1/2),(-1/2,1/2),(-1/2,-3/2)]
def plus : Fin 5 → UnitSquare := fun i => axisSquare (plusCorners i).1 (plusCorners i).2

lemma plus_disjoint : InteriorDisjoint plus := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [plusCorners,AxisSeparated] at *

lemma plus_packing : Packing plus (0,0) (Real.sqrt ((5:ℝ)/2)) := by
  refine ⟨Real.sqrt_nonneg _,?_,plus_disjoint⟩
  intro i
  have hR : Real.sqrt ((5:ℝ)/2) ^ 2 = 5/2 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · apply axis_contained (B := 1/2) (C := 1/2)
    all_goals first | (rw [hR]; norm_num) | norm_num [plus,plusCorners]
  · apply axis_contained (B := 3/2) (C := 1/2)
    all_goals first | (rw [hR]; norm_num) | norm_num [plus,plusCorners]
  · apply axis_contained (B := 3/2) (C := 1/2)
    all_goals first | (rw [hR]; norm_num) | norm_num [plus,plusCorners]
  · apply axis_contained (B := 1/2) (C := 3/2)
    all_goals first | (rw [hR]; norm_num) | norm_num [plus,plusCorners]
  · apply axis_contained (B := 1/2) (C := 3/2)
    all_goals first | (rw [hR]; norm_num) | norm_num [plus,plusCorners]

theorem Five.attainment :
    ∃ (S : Fin 5 → UnitSquare) (o : Point), Packing S o Five.radius :=
  ⟨plus,(0,0),plus_packing⟩

/-- The plus in the frame of its disk centre. -/
def Five.centers : Fin 5 → Point := ![(0,0),(1,0),(0,1),(-1,0),(0,-1)]

end SquaresInCircles
