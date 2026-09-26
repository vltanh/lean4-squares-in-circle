import SquaresInCircles.Seven.EasySectors
import SquaresInCircles.Seven.ForwardPositive
import SquaresInCircles.Seven.ForwardNegativeTarget
import SquaresInCircles.Seven.ForwardBothNegative
import SquaresInCircles.Seven.OppositeForward
import SquaresInCircles.Seven.InwardSideAxial
import SquaresInCircles.Seven.InwardAxialAxial
import SquaresInCircles.Seven.InwardSideTarget
import SquaresInCircles.Seven.InwardOpposite

/-!
# The gap of `π/3`

The support sums at the gap `π/3` on all four axes, for all signs and labels,
are nonnegative for admissible states and vanish only at contacts: each active
case is one of the sector theorems, and capped labels reduce to active ones.
Since every contact has a state on the circle, the sums are positive for
strictly admissible states.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Exhaustive A/T partition, with no omitted axis or sign. -/
theorem fixed_gap_active (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v) :
    PairProperty a u A v s t k := by
  fin_cases k
  · exact .of_pos (fixed_gap_outward h h' s t)
  · cases s <;> cases t
    · exact .of_pos (fixed_gap_forward_positive h h')
    · exact fixed_gap_forward_negative_target .positive h h' (Or.inl rfl) hb
    · exact fixed_gap_forward_opposite_active h h' ha hb
    · rcases ha with hA | hT
      · exact fixed_gap_forward_negative_target .negative h h' (Or.inr hA) hb
      · exact .of_pos (fixed_gap_forward_both_negative_side h h' hT hb)
  · cases s
    · cases t
      · rcases hb with hB | hT
        · rcases ha with hA | hT'
          · exact .of_pos (inward_axial_axial_pos h h' hA hB)
          · exact inward_side_axial_property h h' hT' hB
        · exact .of_pos (fixed_gap_inward_side_target h h' hT)
      · exact fixed_gap_inward_opposite_active h h' ha hb
    · exact .of_pos (fixed_gap_inward_negative h h' t)
  · exact .of_pos (fixed_gap_backward h h' s t)

/-- Complete fixed-angle support theorem including capped labels. -/
theorem fixed_gap_property (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) :
    PairProperty a u A v s t k :=
  fixed_gap_of_active_cases fixed_gap_active a u A v s t k h h'

lemma fixed_gap_nonneg {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v) :
    0≤pairSupport a u A v s t k gap :=
  (fixed_gap_property a u A v s t k h h').1

/-- A zero of a support sum at the gap `π/3` is a contact. -/
theorem Equality.fixed_gap_zero {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (hz : pairSupport a u A v s t k gap = 0) : OrderedContact a u A v s t :=
  (fixed_gap_property a u A v s t k h h').2 hz

/-- Strict positivity at the gap `π/3` for strictly admissible states. -/
theorem fixed_gap_pos {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v) :
    0<pairSupport a u A v s t k gap := by
  refine (fixed_gap_nonneg s t k h.admissible h'.admissible).lt_of_ne fun hz => ?_
  exact Equality.contact_not_strict
    (Equality.fixed_gap_zero s t k h.admissible h'.admissible hz.symm) h h'

end SquaresInCircles.Seven
