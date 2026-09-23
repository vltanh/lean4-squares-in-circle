import SquaresInCircles.Common.Constructions

/-! The T: three unit squares at the optimal radius `5 * sqrt 17 / 16`, with the
disk centre at the origin. -/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for three unit squares: the distance from the disk centre
to the corners of the T. -/
def Three.radius : ℝ := 5 * Real.sqrt 17 / 16

lemma Three.radius_nonneg : 0 ≤ Three.radius := by
  unfold Three.radius
  positivity

lemma Three.radius_sq : Three.radius ^ 2 = 425 / 256 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  unfold Three.radius
  linarith

/-- The T in the frame of its disk centre: two squares side by side, and one
centred on top of them. -/
def Three.centers : Fin 3 → Point := ![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]

def Three.model : Fin 3 → UnitSquare := fun i => axisSquare (Three.centers i)

lemma Three.model_disjoint : InteriorDisjoint Three.model := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [Three.centers,AxisSeparated] at *

theorem Three.model_packing : Packing Three.model (0,0) Three.radius := by
  refine ⟨Three.radius_nonneg,?_,Three.model_disjoint⟩
  intro i
  fin_cases i <;>
    first
    | (apply axis_contained (B := 1) (C := 13/16) <;>
        norm_num [Three.model,Three.centers,Three.radius_sq]; done)
    | (apply axis_contained (B := 1/2) (C := 19/16) <;>
        norm_num [Three.model,Three.centers,Three.radius_sq])

theorem Three.attainment :
    ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o Three.radius :=
  ⟨Three.model,(0,0),Three.model_packing⟩

end SquaresInCircles
