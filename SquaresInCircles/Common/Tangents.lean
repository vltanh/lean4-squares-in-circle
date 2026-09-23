import SquaresInCircles.Common.Basic

/-!
# Contact tangents and the octagon

The tangent-plus-remainder identity for the farthest-vertex function `phi`
turns a strict radius bound into strict linear constraints at every contact
point. The octagon `P8` is shared by the radial sweep and the four- and
five-square cases; the polygons of the individual cases are in their folders.
-/
noncomputable section
namespace SquaresInCircles

/-- Exact tangent-plus-remainder identity, valid at every contact point. -/
theorem tangent_identity (a b u v : ℝ) :
    phi a b - phi u v =
      2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) + (a-u)^2 + (b-v)^2 := by
  unfold phi; ring

theorem tangent_le {a b u v R2 : ℝ} (h : phi a b ≤ R2) (hc : phi u v = R2) :
    2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) ≤ 0 := by
  have hid := tangent_identity a b u v
  nlinarith [sq_nonneg (a-u), sq_nonneg (b-v)]

theorem tangent_lt {a b u v R2 : ℝ} (h : phi a b < R2) (hc : phi u v = R2) :
    2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) < 0 := by
  have hid := tangent_identity a b u v
  nlinarith [sq_nonneg (a-u), sq_nonneg (b-v)]

def P8 (a b : ℝ) : Prop := 3*a+b ≤ 3 ∧ a+3*b ≤ 3
def P8Strict (a b : ℝ) : Prop := 3*a+b < 3 ∧ a+3*b < 3

end SquaresInCircles
