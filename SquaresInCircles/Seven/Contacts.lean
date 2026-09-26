import SquaresInCircles.Seven.PairModel

/-!
# Contacts

The three kinds of contact between labelled states: two side states, or a side
state and an axial state. A side state is `(1, 1/2)`, on the circle
`φ = 13/4`; an axial state `(a, 0)` keeps `a` free. So every contact has a
state on the circle, and no contact is strictly admissible.
-/
noncomputable section
namespace SquaresInCircles.Seven

namespace TransverseSign

def flip : TransverseSign → TransverseSign
  | .positive => .negative
  | .negative => .positive

lemma coe_flip (s : TransverseSign) : s.flip.coe= -s.coe := by cases s <;> norm_num [flip,coe]
end TransverseSign

namespace Equality

abbrev Side (a u : ℝ) : Prop := a = 1 ∧ u = 1/2
abbrev Axial (a u : ℝ) : Prop := u = 0 ∧ 1/2 ≤ a ∧ a ≤ columnLimit

def OrderedContact (a u A v : ℝ) (s t : TransverseSign) : Prop :=
  (s = .negative ∧ t = .positive ∧ Side a u ∧ Side A v) ∨
  (s = .positive ∧ Side a u ∧ Axial A v) ∨
  (t = .negative ∧ Axial a u ∧ Side A v)

lemma remainder_zero {a u : ℝ} (h : Admissible a u)
    (hz : remainder a u = 0) : Side a u := by
  have he := remainder_identity a u
  have hs := h.slack_nonneg
  exact ⟨by nlinarith [sq_nonneg (u-1/2)],
    by nlinarith [sq_nonneg (a-1)]⟩

lemma axial_of_transverse_zero {a u : ℝ} (h : Admissible a u) (hu : u = 0) :
    Axial a u := ⟨hu,h.2.2.1,h.a_le_sqrt_three⟩

lemma side_label : label 1 (1/2) = Real.pi/6 := by
  have hp := pi_lt_22_over_7
  have hp0 := Real.pi_pos
  unfold label axial side
  rw [min_eq_right (a := (5*(1/2)/4 : ℝ)) (by linarith), min_eq_left (by linarith)]
  ring

lemma axial_label {a u : ℝ} (h : Admissible a u) (ha : Axial a u) :
    label a u = 0 := h.label_zero_iff.mpr ha.1

lemma side_neq_cap : label 1 (1/2) ≠ Real.pi/4 := by
  rw [side_label]
  linarith [Real.pi_pos]

lemma contact_label_not_cap {a u A v : ℝ} {s t : TransverseSign}
    (h : Admissible a u) (h' : Admissible A v)
    (hc : OrderedContact a u A v s t) :
    label a u ≠ Real.pi/4 ∧ label A v ≠ Real.pi/4 := by
  rcases hc with ⟨_,_,hs,ht⟩ | ⟨_,hs,ht⟩ | ⟨_,hs,ht⟩
  · simpa [hs.1,hs.2,ht.1,ht.2] using And.intro side_neq_cap side_neq_cap
  · rw [hs.1,hs.2,axial_label h' ht]
    exact ⟨side_neq_cap,by linarith [Real.pi_pos]⟩
  · rw [ht.1,ht.2,axial_label h hs]
    exact ⟨by linarith [Real.pi_pos],side_neq_cap⟩

lemma reflected_reverse_contact {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact A v a u t.flip s.flip) : OrderedContact a u A v s t := by
  cases s <;> cases t <;>
    simp only [OrderedContact,TransverseSign.flip] at hc ⊢ <;> aesop

/-- Every contact has a side state `(1, 1/2)`, where `φ = 13/4`. -/
lemma contact_not_strict {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact a u A v s t)
    (h : StrictlyAdmissible a u) (h' : StrictlyAdmissible A v) : False := by
  have side {a u : ℝ} (hs : Side a u) (h : StrictlyAdmissible a u) : False := by
    have hp := h.2.2.2
    rw [hs.1,hs.2] at hp
    norm_num [phi,targetSq] at hp
  rcases hc with ⟨-,-,hs,-⟩ | ⟨-,hs,-⟩ | ⟨-,-,hs⟩
  · exact side hs h
  · exact side hs h
  · exact side hs h'

end Equality
end SquaresInCircles.Seven
