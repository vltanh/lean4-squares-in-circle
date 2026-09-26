import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Order lemmas from derivatives

Monotonicity on a closed interval from the sign of the derivative inside it,
and two positivity criteria on an interval: from one value, a small slope and
a lower bound on the second derivative, and from the values at both ends and a
nonpositive second derivative.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma monoOn_of_hasDeriv_nonneg {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, 0 ≤ d x) : MonotoneOn f (Icc l u) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc l u) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).hasDerivWithinAt)
    (by simpa only [interior_Icc] using hs)

lemma antiOn_of_hasDeriv_nonpos {l u : ℝ} {f d : ℝ → ℝ}
    (hc : ContinuousOn f (Icc l u))
    (hd : ∀ x ∈ Ioo l u, HasDerivAt f (d x) x)
    (hs : ∀ x ∈ Ioo l u, d x ≤ 0) : AntitoneOn f (Icc l u) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l u) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).hasDerivWithinAt)
    (by simpa only [interior_Icc] using hs)

/-- A function on `[l, u]` with second derivative at least `3/8` is positive
if at one point its value exceeds `3/4000` and its slope is below `1/400`. -/
lemma positive_of_curvature_and_point {l u x t : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, (3:ℝ)/8 ≤ dd y)
    (hval : (3:ℝ)/4000 < f t) (hslope : |d t| < 1/400) : 0 < f x := by
  let g : ℝ → ℝ := fun y => f y-(3/16)*y^2
  have hg (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt g (d y-(3/8)*y) y := by
    convert (hd y hy).sub (((hasDerivAt_id y).pow 2).const_mul (3/16 : ℝ)) using 1
    · rfl
    · dsimp; ring
  have hc : ConvexOn ℝ (Icc l u) g := convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u)
    (fun y hy => (hg y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hg y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => ((hdd y (interior_subset hy)).sub
      ((hasDerivAt_id y).const_mul (3/8 : ℝ))).hasDerivWithinAt)
    (fun y hy => by linarith [hm y (interior_subset hy)])
  have htan : g t+(d t-(3/8)*t)*(x-t) ≤ g x := by
    rcases lt_trichotomy t x with h | rfl | h
    · have hs := hc.le_slope_of_hasDerivAt ht hx h (hg t ht)
      rw [slope_def_field,le_div_iff₀ (sub_pos.2 h)] at hs
      linarith
    · simp
    · have hs := hc.slope_le_of_hasDerivAt hx ht h (hg t ht)
      rw [slope_def_field,div_le_iff₀ (sub_pos.2 h)] at hs
      linarith
  have hs := abs_lt.mp hslope
  have hsq : (d t)^2 < (1/400:ℝ)^2 := by nlinarith
  have hcomplete := sq_nonneg ((3/8)*(x-t)+d t)
  dsimp [g] at htan
  linarith

/-- A function on `[l, u]` with nonpositive second derivative is positive if it
is positive at both ends. -/
lemma positive_of_second_nonpos {l u x : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (hf : ContinuousOn f (Icc l u))
    (hdf : ContinuousOn d (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, dd y ≤ 0)
    (hl : 0 < f l) (hu : 0 < f u) : 0 < f x := by
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l u) hdf
    (fun y hy => (hdd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hm y (interior_subset hy))
  have hconc : ConcaveOn ℝ (Icc l u) f := AntitoneOn.concaveOn_of_deriv (convex_Icc l u) hf
    (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (fun a ha b hb hab => by
      rw [(hd a (interior_subset ha)).deriv,(hd b (interior_subset hb)).deriv]
      exact hanti (interior_subset ha) (interior_subset hb) hab)
  exact (lt_min hl hu).trans_le (hconc.min_le_of_mem_Icc
    (left_mem_Icc.mpr (hx.1.trans hx.2)) (right_mem_Icc.mpr (hx.1.trans hx.2)) hx)

end SquaresInCircles.Seven
