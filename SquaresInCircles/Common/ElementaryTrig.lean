import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Small-angle estimates used by the occupied-arc proofs

All decimal-looking constants below are exact rational numbers.  In particular,
no floating-point evaluation, external solver, or `native_decide` is used.
The five-square auxiliary radius is `5/6`, which keeps both the strip and
radial-extension estimates rational.
-/
noncomputable section
open Set
namespace SquaresInCircles

lemma pi_lt_22_over_7 : Real.pi < (22:ℝ)/7 := by
  linarith [Real.pi_lt_d4]

lemma arcsin_ge_self {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ Real.arcsin x := by
  have hh := Real.sin_le (Real.arcsin_nonneg.mpr hx0)
  rw [Real.sin_arcsin (by linarith) hx1] at hh
  exact hh

lemma arcsin_le_self_of_nonpos {x : ℝ} (hx0 : -1 ≤ x) (hx1 : x ≤ 0) :
    Real.arcsin x ≤ x := by
  have hh := arcsin_ge_self (show 0 ≤ -x by linarith) (show -x ≤ 1 by linarith)
  rw [Real.arcsin_neg] at hh
  linarith

/-- A deliberately non-sharp, polynomial upper bound on `[0,3/5]`. -/
lemma arcsin_le_cubic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 3/5) :
    Real.arcsin x ≤ x+x^3/4 := by
  rcases eq_or_lt_of_le hx0 with hzero | hx
  · rw [← hzero]; norm_num
  let t := x+x^3/4
  have hx2 : x^2 ≤ 9/25 := by nlinarith
  have hsmall := mul_nonneg hx0 (show 0 ≤ 9/25-x^2 by linarith)
  have ht0 : 0 < t := by dsimp [t]; positivity
  have ht : t ≤ (109:ℝ)/100*x := by dsimp [t]; linarith
  have htcube : t^3 ≤ ((109:ℝ)/100)^3*x^3 := by
    calc
      t^3 ≤ ((109:ℝ)/100*x)^3 := by gcongr
      _ = _ := by ring
  have hsin := Real.sin_gt_sub_cube ht0
  have hlower : x ≤ t-t^3/6 := by
    dsimp [t] at *
    linarith [pow_nonneg hx0 3]
  have hdom : t ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    have hbound : t < 1 := by linarith
    exact ⟨by linarith [Real.pi_pos],by linarith [Real.two_le_pi]⟩
  exact (Real.arcsin_lt_iff_lt_sin
    (show x ∈ Icc (-1:ℝ) 1 by exact ⟨by linarith,by linarith⟩) hdom).mpr
    (lt_of_le_of_lt hlower hsin) |>.le

/-- A two-point arcsine comparison, proved by the sine midpoint identity. -/
lemma arcsin_sum_gt_of_sin_lt {u v θ : ℝ}
    (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1)
    (hθ : θ ∈ Icc (0:ℝ) (Real.pi/2)) (hs : Real.sin θ < (u+v)/2) :
    2*θ < Real.arcsin u+Real.arcsin v := by
  let A := Real.arcsin u
  let B := Real.arcsin v
  let m := (A+B)/2
  let d := (A-B)/2
  have hA : 0 ≤ A ∧ A ≤ Real.pi/2 :=
    ⟨Real.arcsin_nonneg.mpr hu.1,Real.arcsin_le_pi_div_two _⟩
  have hB : 0 ≤ B ∧ B ≤ Real.pi/2 :=
    ⟨Real.arcsin_nonneg.mpr hv.1,Real.arcsin_le_pi_div_two _⟩
  have hm : m ∈ Icc (0:ℝ) (Real.pi/2) := by dsimp [m]; constructor <;> linarith
  have hid : u+v=2*Real.sin m*Real.cos d := by
    have h₁ := Real.sin_add m d
    have h₂ := Real.sin_sub m d
    have he₁ : m+d=A := by dsimp [m,d]; ring
    have he₂ : m-d=B := by dsimp [m,d]; ring
    rw [he₁] at h₁
    rw [he₂] at h₂
    dsimp [A,B] at h₁ h₂
    rw [Real.sin_arcsin (by linarith [hu.1]) hu.2] at h₁
    rw [Real.sin_arcsin (by linarith [hv.1]) hv.2] at h₂
    linarith
  have hsin0 := Real.sin_nonneg_of_nonneg_of_le_pi hm.1 (by linarith [hm.2,Real.pi_pos])
  have hp := mul_nonneg hsin0 (sub_nonneg.mpr (Real.cos_le_one d))
  have hs' : Real.sin θ < Real.sin m := by linarith
  have hθm : θ < m := by
    by_contra hn
    have hle := Real.strictMonoOn_sin.monotoneOn
      (show m ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hm.1,hm.2,Real.pi_pos])
      (show θ ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hθ.1,hθ.2,Real.pi_pos])
      (le_of_not_gt hn)
    exact (not_le_of_gt hs') hle
  dsimp [m,A,B] at hθm
  linarith

/-- The crude cosine Taylor bound is sufficient with auxiliary radius `5/6`. -/
lemma cos_gt_401_500 {t : ℝ} (ht : |t| ≤ Real.pi/5) :
    (401:ℝ)/500 < Real.cos t := by
  have habs : |t| < (22:ℝ)/35 := by linarith [pi_lt_22_over_7]
  have ht' := abs_lt.mp habs
  have hsq : t^2 < ((22:ℝ)/35)^2 := by nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := t)
  linarith

lemma sin_pi_fifth_lt_three_fifths : Real.sin (Real.pi/5) < 3/5 := by
  have hc := cos_gt_401_500 (t := Real.pi/5)
    (by rw [abs_of_nonneg (by positivity)])
  have hu := Real.sin_sq_add_cos_sq (Real.pi/5)
  by_contra hn
  nlinarith [Real.cos_le_one (Real.pi/5)]

end SquaresInCircles
