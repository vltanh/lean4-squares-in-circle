import SquaresInCircles.Seven.Uniqueness.ClosedParallel
import SquaresInCircles.Seven.AllGaps

/-!
# Closed containment below the gap `π/3`

Strictly admissible states approximate admissible ones, which carries the
support inequalities of the lower bound over to closed containment. Below the
gap `π/3` a leftmost zero then gives strict positivity.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace SquaresInCircles.Seven
namespace Equality

private def mixA (a e : ℝ) := (1-e)*a+e/2
private def mixU (u e : ℝ) := (1-e)*u

private lemma mix_phi (a u e : ℝ) :
    targetSq-phi (mixA a e) (mixU u e) =
      (1-e)*(targetSq-phi a u)+2*e+
      e*(1-e)*((a-1/2)^2+u^2) := by
  unfold targetSq phi mixA mixU
  ring

private lemma mix_strict {a u e : ℝ} (h : Admissible a u)
    (he : 0 < e ∧ e ≤ 1) : StrictlyAdmissible (mixA a e) (mixU u e) := by
  have he0 := he.1.le
  have he1 : 0 ≤ 1-e := by linarith [he.2]
  have hu := mul_nonneg he1 h.1
  have horder := mul_nonneg he1 (sub_nonneg.mpr h.2.1)
  have ha := mul_nonneg he1 (show 0 ≤ a-1/2 by linarith [h.2.2.1])
  have hslack := mul_nonneg he1 h.slack_nonneg
  have hsq := mul_nonneg (mul_nonneg he0 he1)
    (show 0 ≤ (a-1/2)^2+u^2 by positivity)
  refine ⟨?_,?_,?_,?_⟩
  · exact hu
  · dsimp [mixA,mixU]
    nlinarith
  · dsimp [mixA]
    nlinarith
  · have hi := mix_phi a u e
    linarith [he.1]

/-- Admissible states: the support sums are nonnegative up to the gap `π/3`. -/
lemma all_gap_nonneg {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 ≤ g ∧ g ≤ gap) :
    0 ≤ pairSupport a u A v s t k g := by
  let f : ℝ → ℝ := fun e =>
    pairSupport (mixA a e) (mixU u e) (mixA A e) (mixU v e) s t k g
  have hc : Continuous f := by
    unfold f pairSupport support label side axial mixA mixU
    fun_prop
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 ≤ f e := by
    filter_upwards [self_mem_nhdsWithin,
      ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds)] with e he0 he1
    exact (all_gap_support_pos s t k (mix_strict h ⟨he0,he1.le⟩)
      (mix_strict h' ⟨he0,he1.le⟩) hg).le
  have hh : 0 ≤ f 0 := ge_of_tendsto hlim hpos
  simpa [f,mixA,mixU] using hh

/-- Admissible states: the support sums are positive below the gap `π/3`. -/
theorem all_gap_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 ≤ g ∧ g < gap) :
    0 < pairSupport a u A v s t k g := by
  by_cases hg1 : g ≤ 1
  · exact small_gap_support_pos s t k h h' ⟨hg.1,hg1⟩
  · let f : ℝ → ℝ := fun x => pairSupport a u A v s t k x
    have hf : Continuous f := pairSupport_continuous a u A v s t k
    have hnn (x : ℝ) (hx : x ∈ Icc 1 gap) : 0 ≤ f x :=
      all_gap_nonneg s t k h h' ⟨by linarith [hx.1],hx.2⟩
    by_contra hn
    have hg0 : f g = 0 := by
      have hp := hnn g ⟨(lt_of_not_ge hg1).le,hg.2.le⟩
      exact le_antisymm (le_of_not_gt hn) hp
    let K : Set ℝ := Icc 1 g ∩ {x | f x = 0}
    have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
    have hne : K.Nonempty := ⟨g,⟨(lt_of_not_ge hg1).le,le_rfl⟩,hg0⟩
    obtain ⟨x,hx,hfirst⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    have hleft : 0 < f 1 := small_gap_support_pos s t k h h' (g := 1) ⟨by norm_num,le_rfl⟩
    have hxi : x ∈ Ioo 1 gap := by
      refine ⟨?_,hx.1.2.trans_lt hg.2⟩
      by_contra hn
      have hx1 : x = 1 := le_antisymm (le_of_not_gt hn) hx.1.1
      rw [hx1] at hx
      linarith [show f 1 = 0 from hx.2]
    have hmin : ∀ y ∈ Icc 1 gap, f x ≤ f y := by
      intro y hy
      rw [hx.2]
      exact hnn y hy
    have hbefore : ∀ y ∈ Icc 1 gap, y < x → f x < f y := by
      intro y hy hyx
      rw [hx.2]
      by_contra hn
      have hy0 : f y = 0 := le_antisymm (le_of_not_gt hn) (hnn y hy)
      have hyK : y ∈ K := ⟨⟨hy.1,hyx.le.trans hx.1.2⟩,hy0⟩
      have he : x ≤ y := hfirst hyK
      linarith
    let z := cardinalAngle k+Real.pi-x-s.coe*label a u+t.coe*label A v
    by_cases hs : Real.sin z = 0
    · have hp := cardinal_target_pos_below s t k h h' ⟨hxi.1.le,hxi.2⟩ (Or.inl hs)
      change 0 < f x at hp
      rw [hx.2] at hp
      exact (lt_irrefl (0 : ℝ)) hp
    · by_cases hc : Real.cos z = 0
      · have hp := cardinal_target_pos_below s t k h h' ⟨hxi.1.le,hxi.2⟩ (Or.inr hc)
        change 0 < f x at hp
        rw [hx.2] at hp
        exact (lt_irrefl (0 : ℝ)) hp
      · have hp := smooth_leftmost_support_pos s t k h h' hxi hmin hbefore hc hs
        change 0 < f x at hp
        rw [hx.2] at hp
        exact (lt_irrefl (0 : ℝ)) hp

end Equality
end SquaresInCircles.Seven
