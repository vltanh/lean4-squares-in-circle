import SquaresInCircles.Seven.Labels
import SquaresInCircles.Seven.Construction

/-!
# The support function

The support function of the closed square at a state, bounded below by the
points of the square and by the distance of its centre from the disk centre,
and the Cauchy–Schwarz bound for a linear form on the disk of radius `radius`.
-/
noncomputable section
namespace SquaresInCircles.Seven

def support (a b z : ℝ) : ℝ :=
  a*Real.cos z+b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2

lemma point_le_support {a b x y : ℝ}
    (hx : |x-a| ≤ 1/2) (hy : |y-b| ≤ 1/2) (z : ℝ) :
    x*Real.cos z+y*Real.sin z ≤ support a b z := by
  have hx0 : (x-a)*Real.cos z ≤ (1/2)*|Real.cos z| := by
    calc
      _ ≤ |(x-a)*Real.cos z| := le_abs_self _
      _ = |x-a| * |Real.cos z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hy0 : (y-b)*Real.sin z ≤ (1/2)*|Real.sin z| := by
    calc
      _ ≤ |(y-b)*Real.sin z| := le_abs_self _
      _ = |y-b| * |Real.sin z| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hy (abs_nonneg _)
  dsimp [support]
  linarith

lemma center_norm_bound {a u : ℝ} (h : Admissible a u) :
    a^2+u^2 ≤ (Real.sqrt 3-1/2)^2 := by
  let d := Real.sqrt (a^2+u^2)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = a^2+u^2 := Real.sq_sqrt (by positivity)
  have hs : d ≤ a+u := by nlinarith [h.a_nonneg,h.1,mul_nonneg h.a_nonneg h.1]
  have hp := h.2.2.2
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  dsimp [phi,targetSq] at hp
  have hle : d ≤ Real.sqrt 3-1/2 := by nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hle)
    (show 0 ≤ Real.sqrt 3-1/2+d by linarith)
  linarith

lemma direction_width_ge_one (z : ℝ) : 1 ≤ |Real.cos z|+|Real.sin z| := by
  have he : |Real.cos z|^2+|Real.sin z|^2=1 := by
    simp only [sq_abs]
    linarith [Real.sin_sq_add_cos_sq z]
  have hmul := mul_nonneg (abs_nonneg (Real.cos z)) (abs_nonneg (Real.sin z))
  have h0 := abs_nonneg (Real.cos z)
  have h1 := abs_nonneg (Real.sin z)
  nlinarith

lemma support_lower {a b : ℝ} (h : Admissible a |b|) (z : ℝ) :
    1-Real.sqrt 3 ≤ support a b z := by
  have hn : a^2+b^2 ≤ (Real.sqrt 3-1/2)^2 := by
    simpa only [sq_abs] using center_norm_bound h
  have hid : (a*Real.cos z+b*Real.sin z)^2+
      (a*Real.sin z-b*Real.cos z)^2 = a^2+b^2 := by
    calc
      _ = (a^2+b^2)*(Real.sin z^2+Real.cos z^2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring
  have hsq := sq_nonneg (a*Real.sin z-b*Real.cos z)
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hd2 : (a*Real.cos z+b*Real.sin z)^2 ≤ (Real.sqrt 3-1/2)^2 := by
    linarith only [hid,hn,hsq]
  have hdot : -(Real.sqrt 3-1/2) ≤ a*Real.cos z+b*Real.sin z := by
    generalize a*Real.cos z+b*Real.sin z = D at hd2 ⊢
    have hc : 0 ≤ Real.sqrt 3-1/2 := by nlinarith only [hr,hr0]
    by_contra hn
    have hp := mul_pos (show 0 < -D-(Real.sqrt 3-1/2) by linarith)
      (show 0 < -D+(Real.sqrt 3-1/2) by linarith)
    linarith only [hp,hd2]
  have hw := direction_width_ge_one z
  dsimp [support]
  linarith

lemma outward_support_pos {a A B : ℝ}
    (ha : 1/2 ≤ a) (hB : Admissible A |B|) (z : ℝ) :
    0 < a+1/2+support A B z := by
  have hlow := support_lower hB z
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hroot : Real.sqrt 3 < 2 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  linarith

lemma dot_lower_candidate {X Y p r : ℝ} (hXY : X^2+Y^2 ≤ targetSq) :
    -radius * Real.sqrt (p^2+r^2) ≤ p*X+r*Y := by
  have hid : (p*X+r*Y)^2+(p*Y-r*X)^2=(p^2+r^2)*(X^2+Y^2) := by ring
  have hm := mul_le_mul_of_nonneg_left hXY (show 0 ≤ p^2+r^2 by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ p^2+r^2 by positivity)
  have hn : 0 ≤ radius*Real.sqrt (p^2+r^2) := by
    exact mul_nonneg radius_nonneg (Real.sqrt_nonneg _)
  have he : (radius*Real.sqrt (p^2+r^2))^2=targetSq*(p^2+r^2) := by
    rw [mul_pow, radius_sq, hs]
    rfl
  nlinarith [sq_nonneg (p*Y-r*X)]

end SquaresInCircles.Seven
