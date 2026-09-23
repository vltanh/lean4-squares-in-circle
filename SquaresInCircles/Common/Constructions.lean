import SquaresInCircles.Common.Basic

/-! Axis-parallel unit squares: the disjointness and disk-containment tests
used by the attaining packings. -/
noncomputable section
namespace SquaresInCircles

/-- The axis-parallel unit square centred at `c`. -/
def axisSquare (c : Point) : UnitSquare where
  center := c
  cosine := 1
  sine := 0
  unit := by norm_num

lemma axisSquare_local (c p : Point) :
    localX (axisSquare c) p=p.1-c.1 ∧ localY (axisSquare c) p=p.2-c.2 := by
  constructor <;> simp [localX,localY,axisSquare]

def AxisSeparated (p q : Point) : Prop :=
  p.1+1 ≤ q.1 ∨ q.1+1 ≤ p.1 ∨ p.2+1 ≤ q.2 ∨ q.2+1 ≤ p.2

lemma axis_disjoint {p q : Point} (hs : AxisSeparated p q) :
    ∀ x, ¬ (openSquare (axisSquare p) x ∧ openSquare (axisSquare q) x) := by
  rintro x ⟨hp,hq⟩
  simp only [openSquare,(axisSquare_local _ _).1,(axisSquare_local _ _).2,abs_lt] at hp hq
  rcases hs with h | h | h | h <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2,
    hq.1.1,hq.1.2,hq.2.1,hq.2.2]

/-- The square centred at `c` lies in the disk of radius `R` about the origin
when it lies in the box `[-B,B] × [-C,C]` and `B² + C² ≤ R²`. -/
lemma axis_contained {c : Point} {B C R : ℝ}
    (hx0 : -B ≤ c.1-1/2) (hx1 : c.1+1/2 ≤ B) (hy0 : -C ≤ c.2-1/2) (hy1 : c.2+1/2 ≤ C)
    (hR : B^2+C^2 ≤ R^2) :
    ∀ p, closedSquare (axisSquare c) p → inDisk (0,0) R p := by
  intro p hp
  simp only [closedSquare,(axisSquare_local _ _).1,(axisSquare_local _ _).2,abs_le] at hp
  have hx := sq_le_sq' (a := p.1) (b := B) (by linarith [hp.1.1]) (by linarith [hp.1.2])
  have hy := sq_le_sq' (a := p.2) (b := C) (by linarith [hp.2.1]) (by linarith [hp.2.2])
  dsimp [inDisk,normSq,sub]
  linarith

end SquaresInCircles
