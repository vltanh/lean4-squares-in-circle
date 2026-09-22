import ThreeUnitSquaresInCircle.Unified.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Angular budget on the genuine circle

We use Haar measure on `Real.Angle = AddCircle (2*pi)`.  Its total mass is
`2*pi`; a closed metric ball of radius `w ≤ pi` has mass `2*w`.

Witnesses below consist of actual arcs in planar regions.  Angular shadows
are not used.  Open arcs are handled by shrinking every half-width by the
same factor and using `bound_from_shrinks`; thus no assertion about polygon
boundary measures is needed.
-/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace ThreeUnitSquaresInCircle.Unified

local instance : Fact (0 < (2*Real.pi : ℝ)) := ⟨by positivity⟩

abbrev Direction := Real.Angle

def circlePoint (o : Point) (r : ℝ) (θ : Direction) : Point :=
  (o.1+r*θ.cos, o.2+r*θ.sin)

lemma circlePoint_norm (o : Point) (r : ℝ) (θ : Direction) :
    normSq (sub (circlePoint o r θ) o) = r^2 := by
  calc
    _ = r^2*(θ.cos^2+θ.sin^2) := by dsimp [normSq,sub,circlePoint]; ring
    _ = r^2 := by rw [Real.Angle.cos_sq_add_sin_sq]; ring

lemma direction_norm (θ : Direction) : ‖θ‖ = |θ.toReal| := by
  conv_lhs => rw [← Real.Angle.coe_toReal θ]
  apply (AddCircle.norm_coe_eq_abs_iff (2*Real.pi) (by positivity)).2
  simpa only [abs_of_pos (show 0 < 2*Real.pi by positivity), mul_div_cancel_left₀ _
    (show (2:ℝ) ≠ 0 by norm_num)] using θ.abs_toReal_le_pi

lemma direction_dist (θ φ : Direction) : dist θ φ = |(θ-φ).toReal| := by
  rw [dist_eq_norm,direction_norm]

lemma direction_offset (θ φ : Direction) : θ = φ+((θ-φ).toReal : Direction) := by
  rw [Real.Angle.coe_toReal]
  abel

/-- A certified open angular interval contained in an actual planar region. -/
structure OpenArc (o : Point) (r : ℝ) (U : Set Point) where
  center : Direction
  halfWidth : ℝ
  positive : 0 < halfWidth
  atMostPi : halfWidth ≤ Real.pi
  inside : ∀ θ, dist θ center < halfWidth → circlePoint o r θ ∈ U

/-- The measure-theoretic core, independent of squares and their orientations. -/
theorem closed_arc_budget {n : ℕ} (c : Fin n → Direction) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Real.pi)
    (hd : Pairwise (fun i j => Disjoint
      (Metric.closedBall (c i) (w i)) (Metric.closedBall (c j) (w j)))) :
    ∑ i, w i ≤ Real.pi := by
  classical
  have hvol (i : Fin n) :
      volume (Metric.closedBall (c i) (w i)) = ENNReal.ofReal (2*w i) := by
    rw [AddCircle.volume_closedBall (2*Real.pi)]
    rw [min_eq_right (by linarith [(hw i).2])]
  have hd' : (Finset.univ : Finset (Fin n)).toSet.PairwiseDisjoint
      (fun i => Metric.closedBall (c i) (w i)) := by
    intro i hi j hj hij
    exact hd hij
  have hm := measure_biUnion_finset (μ := (volume : Measure Direction)) hd'
    (fun i hi => measurableSet_closedBall)
  have hmu : (∑ i, ENNReal.ofReal (2*w i)) ≤ ENNReal.ofReal (2*Real.pi) := by
    calc
      _ = volume (⋃ i : Fin n, Metric.closedBall (c i) (w i)) := by
        simpa only [Finset.mem_univ,iUnion_true,hvol] using hm.symm
      _ ≤ volume (univ : Set Direction) := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (2*Real.pi) := AddCircle.measure_univ (2*Real.pi)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmu
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at hreal
  have he (i : Fin n) : (ENNReal.ofReal (2*w i)).toReal=2*w i :=
    ENNReal.toReal_ofReal (by nlinarith [(hw i).1])
  simp only [he, ENNReal.toReal_ofReal (show 0 ≤ 2*Real.pi by positivity)] at hreal
  rw [← Finset.mul_sum] at hreal
  linarith

/-- The same budget for open arc witnesses, without boundary-measure assumptions. -/
theorem open_arc_budget {n : ℕ} {o : Point} {r : ℝ} {U : Fin n → Set Point}
    (A : ∀ i, OpenArc o r (U i)) (hd : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∑ i, (A i).halfWidth ≤ Real.pi := by
  apply Cert.bound_from_shrinks (Finset.sum_nonneg (fun i _ => (A i).positive.le))
  intro t ht0 ht1
  have hw (i : Fin n) : 0 ≤ t*(A i).halfWidth ∧ t*(A i).halfWidth ≤ Real.pi := by
    constructor
    · positivity
    · have hh := mul_lt_mul_of_pos_right ht1 (A i).positive
      nlinarith [(A i).atMostPi]
  have hdisj : Pairwise (fun i j => Disjoint
      (Metric.closedBall (A i).center (t*(A i).halfWidth))
      (Metric.closedBall (A j).center (t*(A j).halfWidth))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro θ hi hj
    apply Set.disjoint_left.mp (hd hij) ((A i).inside θ ?_) ((A j).inside θ ?_)
    · have h := mul_lt_mul_of_pos_right ht1 (A i).positive
      exact lt_of_le_of_lt hi (by linarith)
    · have h := mul_lt_mul_of_pos_right ht1 (A j).positive
      exact lt_of_le_of_lt hj (by linarith)
  simpa only [Finset.mul_sum] using closed_arc_budget (fun i => (A i).center)
    (fun i => t*(A i).halfWidth) hw hdisj

lemma arc_excess_impossible {n : ℕ} {o : Point} {r : ℝ} {U : Fin n → Set Point}
    (A : ∀ i, OpenArc o r (U i)) (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hexcess : Real.pi < ∑ i, (A i).halfWidth) : False :=
  (not_lt_of_ge (open_arc_budget A hd)) hexcess

/-- Uniform lower bounds, with one strict margin, suffice for a contradiction. -/
theorem uniform_arc_excess {n : ℕ} (hn : 0 < n) {o : Point} {r : ℝ}
    {U : Fin n → Set Point} (A : ∀ i, OpenArc o r (U i))
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hle : ∀ i, Real.pi/(n:ℝ) ≤ (A i).halfWidth)
    (hlt : ∃ i, Real.pi/(n:ℝ) < (A i).halfWidth) : False := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsum := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => hle i) (by obtain ⟨i,hi⟩ := hlt; exact ⟨i,Finset.mem_univ _,hi⟩)
  have hconst : (∑ _i : Fin n, Real.pi/(n:ℝ)) = Real.pi := by
    simp [nsmul_eq_mul,hnR]
  rw [hconst] at hsum
  exact arc_excess_impossible A hd hsum

/-- Convert a real parameter interval to an arc on the quotient circle.
The hypotheses contain *strict* planar membership throughout the interval. -/
def arcOfInterval (o : Point) (r : ℝ) (U : Set Point) (phase : Direction)
    (l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u, circlePoint o r (phase+(t:Direction)) ∈ U) :
    OpenArc o r U where
  center := phase+(((l+u)/2 : ℝ) : Direction)
  halfWidth := (u-l)/2
  positive := by linarith
  atMostPi := by linarith
  inside := by
    intro θ hθ
    let s : ℝ := (θ-(phase+(((l+u)/2 : ℝ) : Direction))).toReal
    have hs : |s| < (u-l)/2 := by simpa only [direction_dist] using hθ
    have ht : (l+u)/2+s ∈ Ioo l u := by
      rcases abs_lt.mp hs with ⟨hs₀,hs₁⟩
      exact ⟨by linarith,by linarith⟩
    have he : θ=phase+(((l+u)/2+s : ℝ) : Direction) := by
      rw [Real.Angle.coe_add]
      have hh := direction_offset θ (phase+(((l+u)/2 : ℝ) : Direction))
      simpa only [add_assoc] using hh
    rw [he]
    exact hmem _ ht

end ThreeUnitSquaresInCircle.Unified
