import ThreeUnitSquaresInCircle.Geometry

/-! Algebraic parts of the center estimate, chain contradiction, and Hessian test.
Status: compiles against Lean 4.34.0 / mathlib v4.34.0. -/

noncomputable section
namespace ThreeUnitSquaresInCircle

lemma center_bound_algebra {r : ℝ} (_hr : 0 ≤ r)
    (h : r ^ 2 + r + 1 / 2 ≤ targetSq) : r ≤ 11 / 16 := by
  unfold targetSq at h
  nlinarith [sq_nonneg (r - 11 / 16)]

/--
The tightest numeric step in the development. The slack is
`5/8 - (93/176) * phi`, which at the endpoint `phi = 22/21` equals exactly
`1/14`, so this closes on an equality rather than with room to spare.

The hypothesis `phi ≤ 22/21` comes from `pi/3 ≤ 22/21` (that is, `pi ≤ 22/7`),
whose own margin is about `0.00042`. Widening the angle domain, loosening the
argument range, or re-deriving the bound on `pi` will break this lemma before
anything else, and with it `forbidden_chain`, which eliminates ten of the
sixteen cardinal patterns. Change the constants here only together.
-/
lemma chain_gap {phi : ℝ} (hphi : phi ≤ 22 / 21) :
    (11 / 8 : ℝ) + 11 / 16 * phi + 1 / 14 ≤ 2 + 7 / 44 * phi := by
  linarith

lemma chain_contradiction {phi L : ℝ} (hphi : phi ≤ 22 / 21)
    (hlo : 2 + 7 / 44 * phi ≤ L)
    (hhi : L ≤ 11 / 8 + 11 / 16 * phi) : False := by
  have hgap := chain_gap hphi
  linarith

/-- Positivity of a 2-by-2 quadratic form from its leading minor and determinant. -/
lemma base_hessian_nonneg (ta tb td x y : ℝ)
    (hA : 0 < ta + td)
    (hdet : 0 < ta * tb + ta * td + tb * td) :
    0 ≤ ta * x ^ 2 + tb * y ^ 2 + td * (y - x) ^ 2 := by
  apply le_of_not_gt
  intro hQ
  have hneg := mul_neg_of_pos_of_neg hA hQ
  have heq :
      (ta + td) * (ta * x ^ 2 + tb * y ^ 2 + td * (y - x) ^ 2) =
      ((ta + td) * x - td * y) ^ 2 +
      (ta * tb + ta * td + tb * td) * y ^ 2 := by ring
  rw [heq] at hneg
  have hs := sq_nonneg ((ta + td) * x - td * y)
  have hp := mul_nonneg (le_of_lt hdet) (sq_nonneg y)
  linarith

/-- Increasing each of the three coefficients preserves the quadratic inequality. -/
lemma hessian_nonneg (ga gb gd ta tb td x y : ℝ)
    (ha : ta ≤ ga) (hb : tb ≤ gb) (hd : td ≤ gd)
    (hA : 0 < ta + td)
    (hdet : 0 < ta * tb + ta * td + tb * td) :
    0 ≤ ga * x ^ 2 + gb * y ^ 2 + gd * (y - x) ^ 2 := by
  have hbase := base_hessian_nonneg ta tb td x y hA hdet
  have h0 := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg x)
  have h1 := mul_nonneg (sub_nonneg.mpr hb) (sq_nonneg y)
  have h2 := mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (y - x))
  nlinarith

end ThreeUnitSquaresInCircle
