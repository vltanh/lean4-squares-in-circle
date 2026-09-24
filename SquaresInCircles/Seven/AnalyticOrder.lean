import SquaresInCircles.Seven.ArcAnalysis

/-!
# Order lemmas for the analytical boundary certificates

The conclusions cover whole real intervals. The proofs use monotonicity of
explicit derivatives, not a mesh of derivative values.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma tangent_lower_of_mono_derivative {l u x t : ℝ} {f d : ℝ → ℝ}
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hf : ContinuousOn f (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hmono : MonotoneOn d (Icc l u)) :
    f t+d t*(x-t) ≤ f x := by
  let g : ℝ → ℝ := fun y => f y-f t-d t*(y-t)
  have hgc : ContinuousOn g (Icc l u) := by
    dsimp [g]
    exact (hf.sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hgd (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt g (d y-d t) y := by
    convert ((hd y hy).sub_const (f t)).sub
      (((hasDerivAt_id y).sub_const t).const_mul (d t)) using 1 <;>
      simp [g]
  have hz : g t=0 := by dsimp [g]; ring
  by_cases hxt : t ≤ x
  · have hsub : Icc t x ⊆ Icc l u := by intro y hy; constructor <;> linarith [hx.1,hx.2,ht.1,ht.2,hy.1,hy.2]
    have hm : MonotoneOn g (Icc t x) := monoOn_of_hasDeriv_nonneg
      (hgc.mono hsub)
      (fun y hy => hgd y (hsub ⟨hy.1.le,hy.2.le⟩))
      (fun y hy => sub_nonneg.mpr (hmono ht (hsub ⟨hy.1.le,hy.2.le⟩) hy.1.le))
    have hh := hm ⟨le_rfl,hxt⟩ ⟨hxt,le_rfl⟩ hxt
    rw [hz] at hh
    dsimp [g] at hh
    linarith
  · have hxt' : x ≤ t := le_of_not_ge hxt
    have hsub : Icc x t ⊆ Icc l u := by intro y hy; constructor <;> linarith [hx.1,hx.2,ht.1,ht.2,hy.1,hy.2]
    have hm : AntitoneOn g (Icc x t) := antiOn_of_hasDeriv_nonpos
      (hgc.mono hsub)
      (fun y hy => hgd y (hsub ⟨hy.1.le,hy.2.le⟩))
      (fun y hy => sub_nonpos.mpr (hmono (hsub ⟨hy.1.le,hy.2.le⟩) ht hy.2.le))
    have hh := hm ⟨le_rfl,hxt'⟩ ⟨hxt',le_rfl⟩ hxt'
    rw [hz] at hh
    dsimp [g] at hh
    linarith

lemma quadratic_tangent_lower {l u x t m : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hf : ContinuousOn f (Icc l u)) (hdf : ContinuousOn d (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, m ≤ dd y) :
    f t+d t*(x-t)+(m/2)*(x-t)^2 ≤ f x := by
  let g : ℝ → ℝ := fun y => f y-(m/2)*y^2
  let dg : ℝ → ℝ := fun y => d y-m*y
  have hgc : ContinuousOn g (Icc l u) := by
    dsimp [g]
    exact hf.sub (continuousOn_const.mul (continuousOn_id.pow 2))
  have hdgc : ContinuousOn dg (Icc l u) := by
    dsimp [dg]
    exact hdf.sub (continuousOn_const.mul continuousOn_id)
  have hgd (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt g (dg y) y := by
    convert (hd y hy).sub (((hasDerivAt_id y).pow 2).const_mul (m/2)) using 1 <;>
      dsimp [g,dg] <;> ring
  have hdgd (y : ℝ) (hy : y ∈ Icc l u) : HasDerivAt dg (dd y-m) y := by
    convert (hdd y hy).sub ((hasDerivAt_id y).const_mul m) using 1 <;>
      dsimp [dg] <;> ring
  have hmono : MonotoneOn dg (Icc l u) := monoOn_of_hasDeriv_nonneg hdgc
    (fun y hy => hdgd y ⟨hy.1.le,hy.2.le⟩)
    (fun y hy => sub_nonneg.mpr (hm y ⟨hy.1.le,hy.2.le⟩))
  have hh := tangent_lower_of_mono_derivative hx ht hgc hgd hmono
  dsimp [g,dg] at hh
  nlinarith

lemma positive_of_curvature_and_point {l u x t : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (ht : t ∈ Icc l u)
    (hf : ContinuousOn f (Icc l u)) (hdf : ContinuousOn d (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, (3:ℝ)/8 ≤ dd y)
    (hval : (3:ℝ)/4000 < f t) (hslope : |d t| < 1/400) : 0 < f x := by
  have htan := quadratic_tangent_lower hx ht hf hdf hd hdd hm
  have hs := abs_lt.mp hslope
  have hsq : (d t)^2 < (1/400:ℝ)^2 := by nlinarith
  have hcomplete := sq_nonneg ((3/8)*(x-t)+d t)
  nlinarith

lemma min_endpoints_of_anti_derivative {l u x : ℝ} {f d : ℝ → ℝ}
    (hx : x ∈ Icc l u) (hf : ContinuousOn f (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hanti : AntitoneOn d (Icc l u)) : min (f l) (f u) ≤ f x := by
  by_cases hdx : 0 ≤ d x
  · have hsub : Icc l x ⊆ Icc l u := by
      intro y hy; exact ⟨hy.1,hy.2.trans hx.2⟩
    have hm : MonotoneOn f (Icc l x) := monoOn_of_hasDeriv_nonneg
      (hf.mono hsub)
      (fun y hy => hd y (hsub ⟨hy.1.le,hy.2.le⟩))
      (fun y hy => hdx.trans (hanti (hsub ⟨hy.1.le,hy.2.le⟩) hx hy.2.le))
    exact (min_le_left _ _).trans (hm ⟨le_rfl,hx.1⟩ ⟨hx.1,le_rfl⟩ hx.1)
  · have hdx' : d x ≤ 0 := le_of_not_ge hdx
    have hsub : Icc x u ⊆ Icc l u := by
      intro y hy; exact ⟨hx.1.trans hy.1,hy.2⟩
    have hm : AntitoneOn f (Icc x u) := antiOn_of_hasDeriv_nonpos
      (hf.mono hsub)
      (fun y hy => hd y (hsub ⟨hy.1.le,hy.2.le⟩))
      (fun y hy => (hanti hx (hsub ⟨hy.1.le,hy.2.le⟩) hy.1.le).trans hdx')
    exact (min_le_right _ _).trans (hm ⟨le_rfl,hx.2⟩ ⟨hx.2,le_rfl⟩ hx.2)

lemma min_endpoints_of_second_nonpos {l u x : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (hf : ContinuousOn f (Icc l u))
    (hdf : ContinuousOn d (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, dd y ≤ 0) : min (f l) (f u) ≤ f x := by
  apply min_endpoints_of_anti_derivative hx hf hd
  exact antiOn_of_hasDeriv_nonpos hdf
    (fun y hy => hdd y ⟨hy.1.le,hy.2.le⟩)
    (fun y hy => hm y ⟨hy.1.le,hy.2.le⟩)

lemma positive_of_second_nonpos {l u x : ℝ} {f d dd : ℝ → ℝ}
    (hx : x ∈ Icc l u) (hf : ContinuousOn f (Icc l u))
    (hdf : ContinuousOn d (Icc l u))
    (hd : ∀ y ∈ Icc l u, HasDerivAt f (d y) y)
    (hdd : ∀ y ∈ Icc l u, HasDerivAt d (dd y) y)
    (hm : ∀ y ∈ Icc l u, dd y ≤ 0)
    (hl : 0 < f l) (hu : 0 < f u) : 0 < f x :=
  (lt_min hl hu).trans_le (min_endpoints_of_second_nonpos hx hf hdf hd hdd hm)

/-- A continuous affine image of a segment stays in the quadratic disk when
both endpoints do. The exact nonnegative remainder proves the assertion. -/
lemma phi_segment {a u A v r : ℝ} (hr : 0 ≤ r ∧ r ≤ 1)
    (h : phi a u ≤ targetSq) (h' : phi A v ≤ targetSq) :
    phi ((1-r)*a+r*A) ((1-r)*u+r*v) ≤ targetSq := by
  have hmul := mul_nonneg hr.1 (sub_nonneg.mpr hr.2)
  have hrem := mul_nonneg hmul (add_nonneg (sq_nonneg (a-A)) (sq_nonneg (u-v)))
  have hp := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hr.2)
  have hp' := mul_le_mul_of_nonneg_left h' hr.1
  have hid : phi ((1-r)*a+r*A) ((1-r)*u+r*v) =
      (1-r)*phi a u+r*phi A v-r*(1-r)*((a-A)^2+(u-v)^2) := by
    dsimp [phi]; ring
  rw [hid]
  nlinarith

end SquaresInCircles.Seven
