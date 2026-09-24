import SquaresInCircles.Seven.NearestCornerMinimum
import SquaresInCircles.Seven.SupportPeriodicity

/-!
# All marker gaps up to pi/3

The compact minimization is carried out on the actual support expression.
Its endpoints, nonsmooth cardinal points, and smooth leftmost minima have all
been proved separately. No geometric-reduction proposition is assumed here.
-/
noncomputable section
open Set
namespace SquaresInCircles.Seven

lemma pairSupport_continuous (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) :
    Continuous (fun g => pairSupport a u A v s t k g) := by
  unfold pairSupport support
  fun_prop

/-- The support sum is positive in every edge-source direction whenever the
markers have gap at most pi/3 and the original two containments are strict. -/
theorem all_gap_support_pos {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v)
    (hg : 0≤g ∧ g≤gap) : 0<pairSupport a u A v s t k g := by
  by_cases hg1 : g≤1
  · exact small_gap_support_pos s t k h.admissible h'.admissible ⟨hg.1,hg1⟩
  · by_contra hn
    have hbad : pairSupport a u A v s t k g≤0 := le_of_not_gt hn
    have hleft := small_gap_support_pos s t k h.admissible h'.admissible
      (g := 1) ⟨by norm_num,le_rfl⟩
    have hright := fixed_gap_pos s t k h h'
    obtain ⟨x,hx,hxmin,hmin,hbefore⟩ := leftmost_nonpositive_minimum
      (pairSupport_continuous a u A v s t k)
      ⟨(lt_of_not_ge hg1).le,hg.2⟩ hbad hleft hright
    let z := cardinalAngle k+Real.pi-x-s.coe*label a u+t.coe*label A v
    by_cases hs : Real.sin z=0
    · have hp := cardinal_target_support_pos s t k h h' ⟨hx.1.le,hx.2.le⟩ (Or.inl hs)
      linarith
    · by_cases hc : Real.cos z=0
      · have hp := cardinal_target_support_pos s t k h h' ⟨hx.1.le,hx.2.le⟩ (Or.inr hc)
        linarith
      · have hp := smooth_leftmost_support_pos s t k h.admissible h'.admissible
          hx hmin hbefore hc hs
        linarith

end SquaresInCircles.Seven
