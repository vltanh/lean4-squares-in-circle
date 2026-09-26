import SquaresInCircles.Seven.SmallAndParallelGaps
import SquaresInCircles.Seven.NearestCornerMinimum
import SquaresInCircles.Seven.FixedGap

/-!
# All marker gaps below `π/3`

The support sums of an admissible pair are positive for every gap in
`[0, π/3)`. Gaps up to 1 are small; for larger ones a nonpositive value, with
the sum nonnegative at `π/3`, forces a leftmost minimum inside `[1, π/3]`,
which is either at a cardinal target direction or a smooth stationary point,
and both are positive.
-/
noncomputable section
namespace SquaresInCircles.Seven

lemma pairSupport_continuous (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) :
    Continuous (fun g => pairSupport a u A v s t k g) := by
  unfold pairSupport support
  fun_prop

/-- Admissible states: the support sums are positive below the gap `π/3`. -/
theorem Equality.all_gap_pos_below {a u A v g : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) (hg : 0 ≤ g ∧ g < gap) :
    0 < pairSupport a u A v s t k g := by
  by_cases hg1 : g≤1
  · exact small_gap_support_pos s t k h h' ⟨hg.1,hg1⟩
  · by_contra hn
    have hbad : pairSupport a u A v s t k g≤0 := le_of_not_gt hn
    have hleft := small_gap_support_pos s t k h h' (g := 1) ⟨by norm_num,le_rfl⟩
    have hright := fixed_gap_nonneg s t k h h'
    obtain ⟨x,hx,hxmin,hmin,hbefore⟩ := leftmost_nonpositive_minimum
      (pairSupport_continuous a u A v s t k)
      ⟨(lt_of_not_ge hg1).le,hg.2⟩ hbad hleft hright
    let z := cardinalAngle k+Real.pi-x-s.coe*label a u+t.coe*label A v
    by_cases hs : Real.sin z=0
    · have hp := cardinal_target_pos_below s t k h h' ⟨hx.1.le,hx.2⟩ (Or.inl hs)
      linarith
    · by_cases hc : Real.cos z=0
      · have hp := cardinal_target_pos_below s t k h h' ⟨hx.1.le,hx.2⟩ (Or.inr hc)
        linarith
      · have hp := smooth_leftmost_support_pos s t k h h' hx hmin hbefore hc hs
        linarith

end SquaresInCircles.Seven
