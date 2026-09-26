import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Taylor bounds for sine and cosine

Taylor polynomials of degrees 4 to 7 bound `sin` and `cos` on `[0, ∞)`, by
monotonicity of the remainders.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

/-- A differentiable function that vanishes at `0` and has a nonnegative
derivative on `[0, ∞)` is nonnegative there. -/
lemma nonneg_of_deriv_nonneg (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hzero : f 0 = 0) (hder : ∀ x, 0 ≤ x → 0 ≤ deriv f x)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x :=
  hzero ▸ monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
    hf.differentiableOn (fun t ht => hder t (interior_subset ht)) self_mem_Ici hx hx

lemma cos_upper_four {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24 := by
  let f : ℝ → ℝ := fun t => 1-t^2/2+t^4/24-Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t-t+t^3/6 := by
    simp (disch := fun_prop) [f]
    ring
  have h := nonneg_of_deriv_nonneg f (by dsimp [f]; fun_prop)
    (by norm_num [f]) (fun t ht => by
      rw [hd]
      linarith [Real.sin_ge_sub_cube ht]) hx
  dsimp [f] at h
  linarith

lemma sin_upper_five {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120 := by
  let f : ℝ → ℝ := fun t => t-t^3/6+t^5/120-Real.sin t
  have hd (t : ℝ) : deriv f t = 1-t^2/2+t^4/24-Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have h := nonneg_of_deriv_nonneg f (by dsimp [f]; fun_prop)
    (by norm_num [f]) (fun t ht => by rw [hd]; linarith [cos_upper_four ht]) hx
  dsimp [f] at h
  linarith

lemma cos_lower_six {x : ℝ} (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  let f : ℝ → ℝ := fun t => Real.cos t-(1-t^2/2+t^4/24-t^6/720)
  have hd (t : ℝ) : deriv f t = t-t^3/6+t^5/120-Real.sin t := by
    simp (disch := fun_prop) [f]
    ring
  have h := nonneg_of_deriv_nonneg f (by dsimp [f]; fun_prop)
    (by norm_num [f]) (fun t ht => by rw [hd]; linarith [sin_upper_five ht]) hx
  dsimp [f] at h
  linarith

lemma sin_lower_seven {x : ℝ} (hx : 0 ≤ x) :
    x-x^3/6+x^5/120-x^7/5040 ≤ Real.sin x := by
  let f : ℝ → ℝ := fun t => Real.sin t-(t-t^3/6+t^5/120-t^7/5040)
  have hd (t : ℝ) : deriv f t = Real.cos t-(1-t^2/2+t^4/24-t^6/720) := by
    simp (disch := fun_prop) [f]
    ring
  have h := nonneg_of_deriv_nonneg f (by dsimp [f]; fun_prop)
    (by norm_num [f]) (fun t ht => by rw [hd]; linarith [cos_lower_six ht]) hx
  dsimp [f] at h
  linarith

lemma cos_sq_lower_six {x : ℝ} (hx : 0 ≤ x) :
    1-x^2+x^4/3-2*x^6/45 ≤ Real.cos x^2 := by
  have h := cos_lower_six (show 0 ≤ 2*x by linarith)
  rw [Real.cos_two_mul] at h
  linarith

end SquaresInCircles.Seven
