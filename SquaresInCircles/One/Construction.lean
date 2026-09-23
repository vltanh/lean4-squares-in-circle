import SquaresInCircles.Common.Constructions

/-! The unit square centred at the disk centre, at the optimal radius `sqrt 2 / 2`. -/
noncomputable section
namespace SquaresInCircles

/-- The optimal radius for one unit square: half the diagonal of the square. -/
def One.radius : ℝ := Real.sqrt 2 / 2

lemma One.radius_nonneg : 0 ≤ One.radius := by
  unfold One.radius
  positivity

lemma One.radius_sq : One.radius ^ 2 = 1 / 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold One.radius
  linarith

/-- The square in the frame of its disk centre. -/
def One.centers : Fin 1 → Point := ![(0,0)]

/-- The unit square centred at the origin. -/
def One.model : Fin 1 → UnitSquare := fun i => axisSquare (One.centers i)

theorem One.model_packing : Packing One.model (0,0) One.radius := by
  refine ⟨One.radius_nonneg,?_,?_⟩
  · intro i
    fin_cases i
    apply axis_contained (B := 1/2) (C := 1/2) <;> norm_num [One.centers,One.radius_sq]
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

theorem One.attainment :
    ∃ (S : Fin 1 → UnitSquare) (o : Point), Packing S o One.radius :=
  ⟨One.model,(0,0),One.model_packing⟩

end SquaresInCircles
