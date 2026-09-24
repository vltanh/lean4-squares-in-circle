import SquaresInCircles.Seven.OppositeForward
import SquaresInCircles.Seven.ForwardNegativeTarget
import SquaresInCircles.Seven.ForwardBothNegative
import SquaresInCircles.Seven.InwardSideTarget
import SquaresInCircles.Seven.InwardOpposite

/-!
# Complete fixed-pi/3 support partition

There are four source cardinal normals and four transverse sign pairs. Each
active-label case is discharged by a proved sector theorem; the capped label
is handled by its exact barycentric decomposition. Both closed nonnegativity
and strict positivity under strict original containment are propagated.

This assembly does not yet identify the real support sum of an arbitrary pair
of square charts; that geometric transport is proved separately.
-/
noncomputable section
namespace SquaresInCircles.Seven

private lemma property_of_positive {a u A v : ℝ} {s t : TransverseSign} {k : Fin 4}
    (hp : 0<pairSupport a u A v s t k gap) : PairProperty a u A v s t k :=
  ⟨hp.le,fun _ _ => hp⟩

/-- Exhaustive A/T partition, with no omitted axis or sign. -/
theorem fixed_gap_active (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v) :
    PairProperty a u A v s t k := by
  fin_cases k
  · exact property_of_positive (fixed_gap_outward h h' s t)
  · cases s <;> cases t
    · exact property_of_positive (fixed_gap_forward_positive h h')
    · exact fixed_gap_forward_negative_target .positive h h' (Or.inl rfl) hb
    · exact fixed_gap_forward_opposite_active h h' ha hb
    · rcases ha with hA | hT
      · exact fixed_gap_forward_negative_target .negative h h' (Or.inr hA) hb
      · exact property_of_positive (fixed_gap_forward_both_negative_side h h' hT hb)
  · cases s
    · cases t
      · rcases hb with hB | hT
        · rcases ha with hA | hT'
          · exact property_of_positive (inward_axial_axial_pos h h' hA hB)
          · exact ⟨inward_side_axial_nonneg h h' hT' hB,
              fun hs _ => inward_side_axial_pos hs h' hT' hB⟩
        · exact property_of_positive (fixed_gap_inward_side_target h h' hT)
      · exact fixed_gap_inward_opposite_active h h' ha hb
    · exact property_of_positive (fixed_gap_inward_negative h h' t)
  · exact property_of_positive (fixed_gap_backward h h' s t)

/-- Complete fixed-angle support theorem including capped labels. -/
theorem fixed_gap_property (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) :
    PairProperty a u A v s t k :=
  fixed_gap_of_active_cases fixed_gap_active a u A v s t k h h'

lemma fixed_gap_nonneg {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) :
    0≤pairSupport a u A v s t k gap :=
  (fixed_gap_property a u A v s t k h h').1

/-- The theorem used by the strict-radius contradiction. Original states,
not only their selected endpoints, satisfy the strict hypotheses here. -/
theorem fixed_gap_pos {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v) :
    0<pairSupport a u A v s t k gap :=
  (fixed_gap_property a u A v s t k h.admissible h'.admissible).2 h h'

end SquaresInCircles.Seven
