import SquaresInCircles.Seven.Uniqueness.ClosedLabels

/-!
# Equality types for an ordered pi/3 marker gap

The axial kind carries no chosen radial coordinate. Its admissible interval
will come from containment, not from an isolated-root assumption.
-/
noncomputable section
namespace SquaresInCircles.Seven.Uniqueness

inductive Kind where
  | lower
  | upper
  | axial
  deriving DecidableEq, Fintype

def Kind.next : Kind → Kind
  | .lower => .upper
  | .upper => .axial
  | .axial => .lower

def Kind.flip : Kind → Kind
  | .lower => .upper
  | .upper => .lower
  | .axial => .axial

def Kind.offset : Kind → ℝ
  | .lower => -Real.pi/6
  | .upper => Real.pi/6
  | .axial => 0

def Kind.turn : Kind → ℝ
  | .lower => 0
  | .upper => Real.pi/2
  | .axial => Real.pi/2

def HasKind (k : Kind) (a u : ℝ) (s : TransverseSign) : Prop :=
  match k with
  | .lower => a=1 ∧ u=1/2 ∧ s=.negative
  | .upper => a=1 ∧ u=1/2 ∧ s=.positive
  | .axial => u=0

/-- These are the three directed contacts, not an assumption about a packing. -/
def ContactNext (a u A v : ℝ) (s t : TransverseSign) : Prop :=
  ∃ k : Kind, HasKind k a u s ∧ HasKind k.next A v t

lemma kind_unique {k l : Kind} {a u : ℝ} {s : TransverseSign}
    (hk : HasKind k a u s) (hl : HasKind l a u s) : k=l := by
  cases k <;> cases l <;> simp_all [HasKind]

lemma kind_offset {k : Kind} {a u : ℝ} {s : TransverseSign}
    (h : Admissible a u) (hk : HasKind k a u s) :
    s.coe*label a u=k.offset := by
  cases k
  · rcases hk with ⟨rfl,rfl,rfl⟩
    simp [Kind.offset,TransverseSign.coe,side_contact_label]
  · rcases hk with ⟨rfl,rfl,rfl⟩
    simp [Kind.offset,TransverseSign.coe,side_contact_label]
  · change u=0 at hk
    subst u
    simp [Kind.offset,h.label_zero_iff.mpr rfl]

lemma kind_turn (k : Kind) : gap+k.offset-k.next.offset=k.turn := by
  cases k <;> dsimp [gap,Kind.offset,Kind.next,Kind.turn] <;> ring

lemma kind_flip {k : Kind} {a u : ℝ} {s : TransverseSign}
    (hk : HasKind k a u s) : HasKind k.flip a u s.flip := by
  cases k <;> simp_all [HasKind,Kind.flip,TransverseSign.flip]

lemma contactNext_reflect_reverse {a u A v : ℝ} {s t : TransverseSign}
    (h : ContactNext A v a u t.flip s.flip) : ContactNext a u A v s t := by
  obtain ⟨k,hk,hl⟩ := h
  have hf₁ := kind_flip hl
  have hf₂ := kind_flip hk
  cases k <;>
    simp only [Kind.next,Kind.flip,TransverseSign.flip] at hf₁ hf₂ <;>
    first | exact ⟨Kind.lower,hf₁,hf₂⟩
          | exact ⟨Kind.upper,hf₁,hf₂⟩
          | exact ⟨Kind.axial,hf₁,hf₂⟩

lemma hasKind_not_cap {k : Kind} {a u : ℝ} {s : TransverseSign}
    (h : Admissible a u) (hk : HasKind k a u s) : label a u≠Real.pi/4 := by
  cases k
  · rcases hk with ⟨rfl,rfl,hs⟩
    rw [side_contact_label]
    linarith [Real.pi_pos]
  · rcases hk with ⟨rfl,rfl,hs⟩
    rw [side_contact_label]
    linarith [Real.pi_pos]
  · change u=0 at hk
    subst u
    rw [h.label_zero_iff.mpr rfl]
    linarith [Real.pi_pos]

lemma axial_interval {a u : ℝ} (h : Admissible a u)
    (hk : HasKind .axial a u .positive) :
    1/2≤a ∧ a≤columnLimit := by
  exact ⟨h.2.2.1,h.a_le_sqrt_three⟩

end SquaresInCircles.Seven.Uniqueness
