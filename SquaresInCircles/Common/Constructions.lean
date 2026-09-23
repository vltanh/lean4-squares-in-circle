import SquaresInCircles.Common.Basic

/-! Axis-parallel unit squares: the disjointness and disk-containment tests
used by the attaining packings for one, two, four and five squares. -/
noncomputable section
namespace SquaresInCircles

def AxisSeparated (p q : Point) : Prop :=
  p.1+1 ≤ q.1 ∨ q.1+1 ≤ p.1 ∨ p.2+1 ≤ q.2 ∨ q.2+1 ≤ p.2

lemma axis_disjoint {p q : Point} (hs : AxisSeparated p q) :
    ∀ x, ¬ (openSquare (axisSquare p.1 p.2) x ∧ openSquare (axisSquare q.1 q.2) x) := by
  intro x hx
  have hp := (open_axisSquare_iff _ _ _).mp hx.1
  have hq := (open_axisSquare_iff _ _ _).mp hx.2
  rcases hs with h | h | h | h <;> linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
    hq.1,hq.2.1,hq.2.2.1,hq.2.2.2]

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

end SquaresInCircles
