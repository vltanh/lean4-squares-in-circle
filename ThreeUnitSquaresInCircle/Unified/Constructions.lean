import ThreeUnitSquaresInCircle.Unified.Basic
import ThreeUnitSquaresInCircle.Construction

/-! Attainment for the block and plus packings in the unchanged unit-square model. -/
noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

def blockCorners : Fin 4 → Point := ![(-1,-1),(0,-1),(-1,0),(0,0)]
def block : Fin 4 → UnitSquare := fun i => axisSquare (blockCorners i).1 (blockCorners i).2

def plusCorners : Fin 5 → Point :=
  ![(-1/2,-1/2),(1/2,-1/2),(-3/2,-1/2),(-1/2,1/2),(-1/2,-3/2)]
def plus : Fin 5 → UnitSquare := fun i => axisSquare (plusCorners i).1 (plusCorners i).2

def AxisSeparated (p q : Point) : Prop :=
  p.1+1 ≤ q.1 ∨ q.1+1 ≤ p.1 ∨ p.2+1 ≤ q.2 ∨ q.2+1 ≤ p.2

lemma axis_disjoint {p q : Point} (hs : AxisSeparated p q) :
    ∀ x, ¬ (openSquare (axisSquare p.1 p.2) x ∧ openSquare (axisSquare q.1 q.2) x) := by
  intro x hx
  have hp := (open_axisSquare_iff _ _ _).mp hx.1
  have hq := (open_axisSquare_iff _ _ _).mp hx.2
  rcases hs with h | h | h | h <;> linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
    hq.1,hq.2.1,hq.2.2.1,hq.2.2.2]

lemma block_disjoint : InteriorDisjoint block := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [blockCorners,AxisSeparated] at *

lemma plus_disjoint : InteriorDisjoint plus := by
  intro i j hij
  apply axis_disjoint
  fin_cases i <;> fin_cases j <;> norm_num [plusCorners,AxisSeparated] at *

lemma sq_le_of_interval {x B : ℝ} (h0 : -B ≤ x) (h1 : x ≤ B) : x^2 ≤ B^2 := by
  have hh := mul_nonneg (show 0 ≤ x+B by linarith) (show 0 ≤ B-x by linarith)
  nlinarith

lemma axis_contained {x y B C R : ℝ}
    (hx0 : -B ≤ x) (hx1 : x+1 ≤ B) (hy0 : -C ≤ y) (hy1 : y+1 ≤ C)
    (hR : B^2+C^2 ≤ R^2) :
    ∀ p, closedSquare (axisSquare x y) p → inDisk (0,0) R p := by
  intro p hp
  have hh := (closed_axisSquare_iff x y p).mp hp
  have hx := sq_le_of_interval (x := p.1) (B := B) (by linarith [hh.1]) (by linarith [hh.2.1])
  have hy := sq_le_of_interval (x := p.2) (B := C) (by linarith [hh.2.2.1])
    (by linarith [hh.2.2.2])
  dsimp [inDisk,normSq,sub]
  nlinarith

lemma block_packing : PackingN block (0,0) (Real.sqrt 2) := by
  refine ⟨Real.sqrt_nonneg _,?_,block_disjoint⟩
  intro i
  have hR := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  fin_cases i <;> dsimp [block,blockCorners] <;>
    apply axis_contained (B := 1) (C := 1) <;> norm_num

lemma plus_packing : PackingN plus (0,0) (Real.sqrt ((5:ℝ)/2)) := by
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

end ThreeUnitSquaresInCircle.Unified
