import SquaresInCircles.Seven.FixedGap
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Interior minima of the support sinusoid

A leftmost minimizer is used so that an identically constant sign piece cannot
be mistaken for a new stationary case. The smooth case uses Fermat's theorem
and one comparison to the left, rather than an unproved second-derivative test.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Seven

lemma sin_zero_between {x : ℝ} (hx : -Real.pi<x ∧ x<Real.pi)
    (hs : Real.sin x=0) : x=0 := by
  rcases lt_trichotomy x 0 with h | h | h
  · have hp := Real.sin_pos_of_pos_of_lt_pi (show 0< -x by linarith) (by linarith [hx.1])
    rw [Real.sin_neg,hs] at hp
    linarith
  · exact h
  · have hp := Real.sin_pos_of_pos_of_lt_pi h hx.2
    rw [hs] at hp
    linarith

lemma cos_one_between {x : ℝ} (hx : -2*Real.pi<x ∧ x<2*Real.pi)
    (hc : Real.cos x=1) : x=0 := by
  have hhalf : Real.sin (x/2)=0 := by
    have he := Real.cos_two_mul (x/2)
    rw [show 2*(x/2)=x by ring,hc] at he
    have hu := Real.sin_sq_add_cos_sq (x/2)
    nlinarith
  have hh := sin_zero_between (x := x/2)
    ⟨by linarith [hx.1],by linarith [hx.2]⟩ hhalf
  linarith

lemma cos_zero_between {x : ℝ} (hx : -Real.pi/2<x ∧ x<Real.pi)
    (hc : Real.cos x=0) : x=Real.pi/2 := by
  have hs : Real.sin (x-Real.pi/2)=0 := by
    rw [Real.sin_sub]
    simpa using congrArg Neg.neg hc
  have h := sin_zero_between
    (x := x-Real.pi/2) ⟨by linarith [hx.1],by linarith [hx.2,Real.pi_pos]⟩ hs
  linarith

lemma trig_direction_injective {x y : ℝ}
    (hxy : -2*Real.pi<x-y ∧ x-y<2*Real.pi)
    (hc : Real.cos x=Real.cos y) (hs : Real.sin x=Real.sin y) : x=y := by
  have hh : Real.cos (x-y)=1 := by
    rw [Real.cos_sub,hc,hs]
    nlinarith [Real.sin_sq_add_cos_sq y]
  have he := cos_one_between hxy hh
  linarith

lemma cardinal_range (k : Fin 4) : 0≤cardinalAngle k ∧ cardinalAngle k≤3*Real.pi/2 := by
  fin_cases k <;> norm_num [cardinalAngle] <;> (try constructor) <;> linarith [Real.pi_pos]

lemma cardinal_sine_cosine (k : Fin 4) :
    Real.sin (cardinalAngle k)=0 ∨ Real.cos (cardinalAngle k)=0 := by
  fin_cases k <;> norm_num [cardinalAngle,Real.sin_add,Real.cos_add,
    show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring]

/-- A nonpositive value between positive endpoints has an interior leftmost
minimizer. Every earlier point has strictly larger value. -/
lemma leftmost_nonpositive_minimum {f : ℝ → ℝ} {l u y : ℝ}
    (hf : Continuous f) (hy : y∈Icc l u) (hbad : f y≤0)
    (hl : 0<f l) (hu : 0<f u) :
    ∃ x, x∈Ioo l u ∧ f x≤0 ∧
      (∀z∈Icc l u,f x≤f z) ∧
      (∀z∈Icc l u,z<x → f x<f z) := by
  obtain ⟨m,hm,hmin⟩ := isCompact_Icc.exists_isMinOn
    ⟨y,hy⟩ hf.continuousOn
  let K : Set ℝ := Icc l u ∩ {x | f x=f m}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_eq hf continuous_const)
  have hn : K.Nonempty := ⟨m,hm,rfl⟩
  obtain ⟨x,hx,hleft⟩ := hK.exists_isMinOn hn continuous_id.continuousOn
  have hxval : f x=f m := hx.2
  have hxnon : f x≤0 := hxval.le.trans ((hmin hy).trans hbad)
  have hxl : l<x := by
    have hle := hx.1.1
    by_contra hn
    have he : x=l := le_antisymm (le_of_not_gt hn) hle
    rw [he] at hxnon
    linarith
  have hxu : x<u := by
    have hle := hx.1.2
    by_contra hn
    have he : x=u := le_antisymm hle (le_of_not_gt hn)
    rw [he] at hxnon
    linarith
  refine ⟨x,⟨hxl,hxu⟩,hxnon,?_,?_⟩
  · intro z hz
    rw [hxval]
    exact hmin hz
  · intro z hz hzx
    have hle : f x≤f z := hxval.le.trans (hmin hz)
    by_contra hn
    have he : f z=f m := by linarith
    have hk : z∈K := ⟨hz,he⟩
    have hh : x≤z := hleft hk
    linarith

lemma sinusoid_leftmost_minimum {f : ℝ → ℝ} {l u x c A B Z : ℝ}
    (hx : x∈Ioo l u)
    (hmin : ∀y∈Icc l u,f x≤f y)
    (hleft : ∀y∈Icc l u,y<x → f x<f y)
    (hevent : f =ᶠ[𝓝 x] (fun y => c+A*Real.cos (Z-y)+B*Real.sin (Z-y))) :
    A*Real.sin (Z-x)-B*Real.cos (Z-x)=0 ∧
      A*Real.cos (Z-x)+B*Real.sin (Z-x)<0 := by
  let g : ℝ → ℝ := fun y => c+A*Real.cos (Z-y)+B*Real.sin (Z-y)
  have he0 : f x=g x := hevent.eq_of_nhds
  have hlocal : IsLocalMin f x := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hmin y ⟨hy.1.le,hy.2.le⟩
  have harg : HasDerivAt (fun y : ℝ => Z-y) (-1) x := (hasDerivAt_id' x).const_sub Z
  have hg : HasDerivAt g (A*Real.sin (Z-x)-B*Real.cos (Z-x)) x := by
    convert (((harg.cos.const_mul A).const_add c).add (harg.sin.const_mul B)) using 1
    ring
  have hf := hg.congr_of_eventuallyEq hevent
  have hstationary : A*Real.sin (Z-x)-B*Real.cos (Z-x)=0 :=
    hlocal.hasDerivAt_eq_zero hf
  refine ⟨hstationary,?_⟩
  by_contra hn
  have hnon : 0≤A*Real.cos (Z-x)+B*Real.sin (Z-x) := le_of_not_gt hn
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hevent
  let e := min (r/2) ((x-l)/2)
  have hepos : 0<e := lt_min (by positivity) (by linarith [hx.1])
  have her : e<r := (min_le_left _ _).trans_lt (by linarith)
  have hex : e≤(x-l)/2 := min_le_right _ _
  have hy : x-e∈Icc l u := ⟨by linarith,by linarith [hx.2]⟩
  have hyl : x-e<x := by linarith
  have hye : f (x-e)=g (x-e) := hball
    (by rw [Metric.mem_ball,Real.dist_eq,show (x-e)-x=-e by ring,abs_neg,abs_of_pos hepos]; exact her)
  have hstrict := hleft (x-e) hy hyl
  rw [he0,hye] at hstrict
  have hid : g (x-e)-g x=
      (A*Real.cos (Z-x)+B*Real.sin (Z-x))*(Real.cos e-1) := by
    have he : Z-(x-e)=(Z-x)+e := by ring
    dsimp [g]
    rw [he,Real.cos_add,Real.sin_add]
    linear_combination (-Real.sin e)*hstationary
  have hprod := mul_nonpos_of_nonneg_of_nonpos hnon
    (sub_nonpos.mpr (Real.cos_le_one e))
  linarith

lemma absolute_sign_eventually {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ}
    (hx : f x≠0) :
    ∀ᶠ y in 𝓝 x, |f y|=(if 0<f x then (1:ℝ) else -1)*f y := by
  by_cases hpos : 0<f x
  · filter_upwards [(hf.tendsto x).eventually (lt_mem_nhds hpos)] with y hy
    simp only [ite_eq_left hpos,one_mul,abs_of_pos hy]
  · have hneg : f x<0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    filter_upwards [(hf.tendsto x).eventually (gt_mem_nhds hneg)] with y hy
    simp only [ite_eq_right hpos,neg_one_mul,abs_of_neg hy]

end SquaresInCircles.Seven
