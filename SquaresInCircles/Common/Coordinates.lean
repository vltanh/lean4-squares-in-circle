import SquaresInCircles.Common.Charts
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Cartesian access to the square charts

Points in a rotated frame at the disk centre, Cartesian membership recovered
from the all-radius chart identity, and inscribed disks.
-/
noncomputable section
open Set
namespace SquaresInCircles

lemma pointInDirection_polar (o : Point) (phase : Direction) (r t : ℝ) :
    pointInDirection o phase (r*Real.cos t) (r*Real.sin t) =
      circlePoint o r (phase+(t:Direction)) := by
  apply Prod.ext <;>
    simp only [pointInDirection,circlePoint,Real.Angle.cos_add,Real.Angle.sin_add,
      Real.Angle.cos_coe,Real.Angle.sin_coe] <;> ring

lemma pointInDirection_norm (o : Point) (phase : Direction) (x y : ℝ) :
    normSq (sub (pointInDirection o phase x y) o)=x^2+y^2 := by
  calc
    _ = (phase.cos^2+phase.sin^2)*(x^2+y^2) := by
      dsimp [normSq,sub,pointInDirection]; ring
    _ = _ := by rw [Real.Angle.cos_sq_add_sin_sq]; ring

/-- Polar coordinates, from the polar form of the complex number `x + iy`. -/
lemma plane_polar (x y : ℝ) :
    ∃ r t : ℝ, r*Real.cos t=x ∧ r*Real.sin t=y :=
  ⟨_,_,Complex.norm_mul_cos_arg ⟨x,y⟩,Complex.norm_mul_sin_arg ⟨x,y⟩⟩

/-- Reversal of a chart changes only the sign of its transverse center coordinate. -/
def SquareChart.signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) : ℝ :=
  if C.reversed then -C.b else C.b

lemma SquareChart.abs_signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    |C.signedB|=C.b := by
  unfold SquareChart.signedB
  split_ifs <;> simp only [abs_neg,abs_of_nonneg C.nonneg.2]

lemma SquareChart.cartesian {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (x y : ℝ) :
    openSquare S (pointInDirection o C.phase x y) ↔
      |x-C.a| < 1/2 ∧ |y-C.signedB| < 1/2 := by
  obtain ⟨r,t,hx,hy⟩ := plane_polar x y
  rw [← hx,← hy,pointInDirection_polar]
  cases hrev : C.reversed
  · have h := C.membership r t
    simpa only [chartAngle,hrev,Bool.false_eq_true,ite_false,SquareChart.signedB] using h
  · have h := C.membership r (-t)
    have habs : |-(r*Real.sin t)-C.b|=|r*Real.sin t+C.b| := by
      rw [show -(r*Real.sin t)-C.b=-(r*Real.sin t+C.b) by ring,abs_neg]
    simpa only [chartAngle,hrev,ite_true,neg_neg,Real.cos_neg,Real.sin_neg,
      mul_neg,SquareChart.signedB,sub_neg_eq_add,habs] using h

lemma pointInDirection_transition (o : Point) (φ ψ : Direction) (x y : ℝ) :
    pointInDirection o φ x y = pointInDirection o ψ
      ((ψ-φ).cos*x+(ψ-φ).sin*y)
      (-(ψ-φ).sin*x+(ψ-φ).cos*y) := by
  have hu := Real.Angle.cos_sq_add_sin_sq ψ
  apply Prod.ext
  · calc
      _ = o.1+(ψ.cos^2+ψ.sin^2)*(φ.cos*x-φ.sin*y) := by
        dsimp [pointInDirection]
        rw [hu]
        ring
      _ = _ := by
        simp only [pointInDirection,sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,
          Real.Angle.cos_neg,Real.Angle.sin_neg]
        ring
  · calc
      _ = o.2+(ψ.cos^2+ψ.sin^2)*(φ.sin*x+φ.cos*y) := by
        dsimp [pointInDirection]
        rw [hu]
        ring
      _ = _ := by
        simp only [pointInDirection,sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,
          Real.Angle.cos_neg,Real.Angle.sin_neg]
        ring

/-- The disk given by the nearer side of a containing square is really inside it. -/
lemma inscribed_disk_mem (S : UnitSquare) (o : Point) {a p : ℝ}
    (hp : 0 < p) (hpa : a+p=1/2)
    (hx : alpha S o ≤ a) (hy : beta S o ≤ a) {z : Point}
    (hz : normSq (sub z o) < p^2) : openSquare S z := by
  have hu := frame_norm S (sub z o)
  have hX : |frameX S (sub z o)| < p := by
    apply abs_lt.mpr
    constructor <;> nlinarith [sq_nonneg (frameY S (sub z o))]
  have hY : |frameY S (sub z o)| < p := by
    apply abs_lt.mpr
    constructor <;> nlinarith [sq_nonneg (frameX S (sub z o))]
  have heX : localX S z=frameX S (sub z o)+localX S o := by
    dsimp [localX,frameX,sub]; ring
  have heY : localY S z=frameY S (sub z o)+localY S o := by
    dsimp [localY,frameY,sub]; ring
  refine ⟨?_,?_⟩
  · rw [heX]
    have hb := abs_add_le (frameX S (sub z o)) (localX S o)
    change |localX S o| ≤ a at hx
    linarith
  · rw [heY]
    have hb := abs_add_le (frameY S (sub z o)) (localY S o)
    change |localY S o| ≤ a at hy
    linarith

end SquaresInCircles
