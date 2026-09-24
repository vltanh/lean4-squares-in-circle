import SquaresInCircles.Seven.Uniqueness.ClosedLabels
import SquaresInCircles.Seven.AllGaps

/-!
# Closed containment, with strictness below pi/3

Continuity extends the already proved support inequalities to the boundary.
It does NOT give strictness by itself. Strictness for a subcritical marker gap
is proved separately: a leftmost zero is either a parallel-frame minimum or a
smooth nearest-corner minimum, and both have explicit contradictions.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Seven.Equality

def blendA (a t : ℝ) : ℝ := 1/2+t*(a-1/2)
def blendU (u t : ℝ) : ℝ := t*u

lemma blend_strict {a u t : ℝ} (h : Admissible a u) (ht : 0≤t ∧ t<1) :
    StrictlyAdmissible (blendA a t) (blendU u t) := by
  have hlin := mul_nonneg ht.1 (show 0≤a-u by linarith [h.2.1])
  have hbase := mul_nonneg ht.1 (show 0≤a-1/2 by linarith [h.2.2.1])
  have he : phi (blendA a t) (blendU u t)=
      (1-t)*(5/4)+t*phi a u-t*(1-t)*((a-1/2)^2+u^2) := by
    dsimp [blendA,blendU,phi]
    ring
  refine ⟨by dsimp [blendU]; positivity,?_,?_,?_⟩
  · dsimp [blendA,blendU]
    linarith
  · dsimp [blendA]
    linarith
  · rw [he]
    have hs := mul_nonneg (mul_nonneg ht.1 (by linarith : 0≤1-t))
      (show 0≤(a-1/2)^2+u^2 by positivity)
    have hp := mul_le_mul_of_nonneg_left h.2.2.2 ht.1
    dsimp [targetSq] at hp ⊢
    nlinarith

lemma all_gap_support_nonneg {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0≤g ∧ g≤gap) :
    0≤pairSupport a u A v s t k g := by
  let F : ℝ → ℝ := fun x =>
    pairSupport (blendA a x) (blendU u x) (blendA A x) (blendU v x) s t k g
  have hc : Continuous F := by
    dsimp [F,pairSupport,support,blendA,blendU,label,side,axial]
    fun_prop
  have ht : ∀ x∈Ico (0 : ℝ) 1,0≤F x := by
    intro x hx
    exact (all_gap_support_pos s t k (blend_strict h hx) (blend_strict h' hx) hg).le
  have hz : (1 : ℝ)∈closure (Ico (0 : ℝ) 1) := by
    rw [closure_Ico (by norm_num : (0 : ℝ)≠1)]
    norm_num
  have hclosed : IsClosed {x : ℝ | 0≤F x} := isClosed_le continuous_const hc
  have hlim := (closure_minimal ht hclosed) hz
  simpa [F,blendA,blendU] using hlim

lemma parallel_zero_support_closed {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0<g ∧ g<gap)
    (he : g+s.coe*label a u-t.coe*label A v=0) :
    0<pairSupport a u A v s t k g := by
  have hangle : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v=
      cardinalAngle k+Real.pi := by linarith
  rw [pairSupport,hangle,support_add_pi,cardinal_support_sum]
  have h0 := h.label_nonneg
  have h1 := h'.label_nonneg
  have ha := h.a_lt_five_fourths
  have hA := h'.a_lt_five_fourths
  have hu := h.u_lt
  have hv := h'.u_lt
  fin_cases k
  · norm_num
    linarith [h'.2.2.1]
  · by_contra hn
    cases s <;> cases t <;> norm_num [TransverseSign.coe] at hn he ⊢
    · linarith [h.1]
    · linarith [h.1,h'.1]
    · have hs : 1≤u+v := by linarith
      have hl := Uniqueness.opposite_labels_ge h h' hs
      linarith [hg.2]
    · linarith [h'.1]
  · norm_num
    linarith [h.2.2.1]
  · cases s <;> cases t <;> norm_num [TransverseSign.coe] at he ⊢
    · linarith [h'.1]
    · linarith [hg.1]
    · linarith [h.1,h'.1]
    · linarith [h.1]

lemma parallel_quarter_support_closed {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0<g ∧ g<gap)
    (he : g+s.coe*label a u-t.coe*label A v=Real.pi/2) :
    0<pairSupport a u A v s t k g := by
  have hangle : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v=
      cardinalAngle k+Real.pi/2 := by linarith
  rw [pairSupport,hangle,support_add_half_pi,cardinal_support_sum]
  have hu : |s.coe*u|<31/40 := by
    cases s <;> simpa [TransverseSign.coe,abs_of_nonneg h.1] using h.u_lt
  have hv : |t.coe*v|<31/40 := by
    cases t <;> simpa [TransverseSign.coe,abs_of_nonneg h'.1] using h'.u_lt
  have hu' := abs_lt.mp hu
  have hv' := abs_lt.mp hv
  have hlabel (hh : 1≤a+t.coe*v ∨ 1≤A-s.coe*u) : False := by
    have hp := Uniqueness.quarter_difference_le (sign_admissible h s)
      (sign_admissible h' t) hh
    rw [sign_label h s,sign_label h' t] at hp
    dsimp [gap] at hg
    linarith
  fin_cases k
  · norm_num
    linarith [h.2.2.1]
  · by_contra hn
    norm_num at hn
    exact hlabel (Or.inr (by linarith))
  · by_contra hn
    norm_num at hn
    exact hlabel (Or.inl (by linarith))
  · norm_num
    linarith [h'.2.2.1]

lemma cardinal_target_support_closed {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 1≤g ∧ g<gap)
    (hcard : Real.sin (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v)=0 ∨
      Real.cos (cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v)=0) :
    0<pairSupport a u A v s t k g := by
  let d := g+s.coe*label a u-t.coe*label A v
  have hr : -Real.pi/2<d ∧ d<Real.pi := by
    have ht0 := h.label_nonneg
    have ht1 := h.label_le_quarter
    have hs0 := h'.label_nonneg
    have hs1 := h'.label_le_quarter
    cases s <;> cases t <;> dsimp [d,gap,TransverseSign.coe] at * <;>
      constructor <;> linarith [Real.pi_pos]
  have he : cardinalAngle k+Real.pi-g-s.coe*label a u+t.coe*label A v=
      cardinalAngle k+Real.pi-d := by dsimp [d]; ring
  rw [he] at hcard
  rcases cardinal_target_relative k hcard with hs | hc
  · have hd : d=0 := sin_zero_between
      ⟨by linarith [hr.1,Real.pi_pos],hr.2⟩ hs
    exact parallel_zero_support_closed s t k h h' ⟨by linarith [hg.1],hg.2⟩ hd
  · have hd : d=Real.pi/2 := cos_zero_between hr hc
    exact parallel_quarter_support_closed s t k h h' ⟨by linarith [hg.1],hg.2⟩ hd

/-- A leftmost zero before the right endpoint; no positivity is assumed at
that right endpoint, which may itself be an equality contact. -/
lemma leftmost_zero {f : ℝ → ℝ} {l u y : ℝ}
    (hf : Continuous f) (hy : l≤y ∧ y<u) (hzero : f y=0)
    (hl : 0<f l) (hnon : ∀z∈Icc l u,0≤f z) :
    ∃ x, x∈Ioo l u ∧ f x=0 ∧
      (∀z∈Icc l u,f x≤f z) ∧
      (∀z∈Icc l u,z<x → f x<f z) := by
  let K : Set ℝ := Icc l y ∩ {z | f z=0}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
  have hne : K.Nonempty := ⟨y,⟨hy.1,le_rfl⟩,hzero⟩
  obtain ⟨x,hx,hxmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
  have hxl : l<x := by
    by_contra hbad
    have he : x=l := le_antisymm (le_of_not_gt hbad) hx.1.1
    rw [he] at hx
    linarith [hx.2]
  refine ⟨x,⟨hxl,hx.1.2.trans_lt hy.2⟩,hx.2,?_,?_⟩
  · intro z hz
    rw [hx.2]
    exact hnon z hz
  · intro z hz hzx
    have hznon := hnon z hz
    rw [hx.2]
    by_contra hn
    have he : f z=0 := le_antisymm (le_of_not_gt hn) hznon
    have hzk : z∈K := ⟨⟨hz.1,by linarith [hx.1.2]⟩,he⟩
    have hh : x≤z := hxmin hzk
    linarith

/-- Closed states are strictly overlapping in every source direction at every
subcritical marker gap. Only gap = pi/3 can admit a zero. -/
theorem all_gap_support_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0≤g ∧ g<gap) :
    0<pairSupport a u A v s t k g := by
  by_cases hg1 : g≤1
  · exact small_gap_support_pos s t k h h' ⟨hg.1,hg1⟩
  · by_contra hn
    have hzero : pairSupport a u A v s t k g=0 :=
      le_antisymm (le_of_not_gt hn) (all_gap_support_nonneg s t k h h' ⟨hg.1,hg.2.le⟩)
    have hl := small_gap_support_pos s t k h h' (g := 1) ⟨by norm_num,le_rfl⟩
    obtain ⟨x,hx,hzero,hmin,hbefore⟩ := leftmost_zero
      (pairSupport_continuous a u A v s t k)
      ⟨(lt_of_not_ge hg1).le,hg.2⟩ hzero hl
      (fun z hz => all_gap_support_nonneg s t k h h' ⟨by linarith [hz.1],hz.2⟩)
    let z := cardinalAngle k+Real.pi-x-s.coe*label a u+t.coe*label A v
    by_cases hs : Real.sin z=0
    · have hp := cardinal_target_support_closed s t k h h' ⟨hx.1.le,hx.2⟩ (Or.inl hs)
      linarith
    · by_cases hc : Real.cos z=0
      · have hp := cardinal_target_support_closed s t k h h' ⟨hx.1.le,hx.2⟩ (Or.inr hc)
        linarith
      · have hp := smooth_leftmost_support_pos s t k h h' hx hmin hbefore hc hs
        linarith

end SquaresInCircles.Seven.Equality
