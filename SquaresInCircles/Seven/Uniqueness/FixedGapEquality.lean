import SquaresInCircles.Seven.Uniqueness.ScalarEquality

/-!
# Equality in the exhaustive fixed-angle partition

Unlike strict optimality, this theorem identifies every possible zero. The
capped-label reduction preserves zero sets through a positive weighted term;
no assumption of strict containment is made.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

lemma fixed_gap_zero_active {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (ha : ActiveLabel a u) (hb : ActiveLabel A v)
    (hz : pairSupport a u A v s t k gap = 0) :
    OrderedContact a u A v s t := by
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by fin_cases k <;> simp
  · have hp := fixed_gap_outward h h' s t
    rw [hz] at hp
    exact False.elim ((lt_irrefl (0 : ℝ)) hp)
  · cases s <;> cases t
    · have hp := fixed_gap_forward_positive h h'
      rw [hz] at hp
      exact False.elim ((lt_irrefl (0 : ℝ)) hp)
    · have hc := forward_negative_target_zero .positive h h' (Or.inl rfl) hb hz
      exact Or.inr (Or.inr ⟨rfl,hc.1,hc.2⟩)
    · rw [pairSupport_forward_opposite h h'] at hz
      rcases ha with hA | hT <;> rcases hb with hA' | hT'
      · have hp := opposite_axial_axial_pos h h' hA hA'
        rw [hz] at hp
        exact False.elim ((lt_irrefl (0 : ℝ)) hp)
      · have hp := opposite_axial_side_pos h h' hA hT'
        rw [hz] at hp
        exact False.elim ((lt_irrefl (0 : ℝ)) hp)
      · have hp := opposite_side_axial_pos h h' hT hA'
        rw [hz] at hp
        exact False.elim ((lt_irrefl (0 : ℝ)) hp)
      · have hc := side_side_zero h h' hT hT' hz
        exact Or.inl ⟨rfl,rfl,hc.1,hc.2⟩
    · rcases ha with hA | hT
      · have hc := forward_negative_target_zero .negative h h' (Or.inr hA) hb hz
        exact Or.inr (Or.inr ⟨rfl,hc.1,hc.2⟩)
      · have hp := fixed_gap_forward_both_negative_side h h' hT hb
        rw [hz] at hp
        exact False.elim ((lt_irrefl (0 : ℝ)) hp)
  · cases s
    · cases t
      · rcases hb with hA | hT
        · rcases ha with hA' | hT'
          · have hp := inward_axial_axial_pos h h' hA' hA
            rw [hz] at hp
            exact False.elim ((lt_irrefl (0 : ℝ)) hp)
          · have hc := inward_side_axial_eq_zero h h' hT' hA hz
            exact Or.inr (Or.inl ⟨rfl,⟨hc.1,hc.2.1⟩,
              axial_of_transverse_zero h' hc.2.2⟩)
        · have hp := fixed_gap_inward_side_target h h' hT
          rw [hz] at hp
          exact False.elim ((lt_irrefl (0 : ℝ)) hp)
      · rcases hb with hA | hT
        · rcases ha with hA' | hT'
          · have hp := inward_opposite_axial_axial_pos h h' hA' hA
            rw [hz] at hp
            exact False.elim ((lt_irrefl (0 : ℝ)) hp)
          · have hc := inward_opposite_zero h h' hT' hA hz
            exact Or.inr (Or.inl ⟨rfl,hc.1,hc.2⟩)
        · exact False.elim (inward_side_target_ne_zero h h' ha hT hz)
    · have hp := fixed_gap_inward_negative h h' t
      rw [hz] at hp
      exact False.elim ((lt_irrefl (0 : ℝ)) hp)
  · have hp := fixed_gap_backward h h' s t
    rw [hz] at hp
    exact False.elim ((lt_irrefl (0 : ℝ)) hp)

private lemma zero_of_weighted_sum {w f : Fin 3 → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i)
    (hs : ∑ i, w i * f i = 0) {i : Fin 3} (hi : 0 < w i) : f i = 0 := by
  have hle := Finset.single_le_sum
    (fun j _ => mul_nonneg (hw j) (hf j)) (Finset.mem_univ i)
  rw [hs] at hle
  have he : w i * f i = 0 := le_antisymm hle (mul_nonneg (hw i) (hf i))
  exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hi)

/-- Closed containment, all signs, all axes, all active labels. -/
theorem fixed_gap_zero {a u A v : ℝ} (s t : TransverseSign) (k : Fin 4)
    (h : Admissible a u) (h' : Admissible A v)
    (hz : pairSupport a u A v s t k gap = 0) : OrderedContact a u A v s t := by
  have with_active_source (a u A v : ℝ) (h : Admissible a u) (h' : Admissible A v)
      (ha : ActiveLabel a u)
      (hz : pairSupport a u A v s t k gap = 0) : OrderedContact a u A v s t := by
    rcases h'.selected with hA | hT | hcap
    · exact fixed_gap_zero_active s t k h h' ha (Or.inl hA) hz
    · exact fixed_gap_zero_active s t k h h' ha (Or.inr hT) hz
    · obtain ⟨i,hi⟩ := capWeights_some_pos h' hcap
      have hsum := hz
      rw [cap_pair_second hcap] at hsum
      have hzi := zero_of_weighted_sum
        (capWeights_nonneg h' hcap)
        (fun j => fixed_gap_nonneg s t k h (capVertex_strict j).admissible)
        hsum hi
      have hc := fixed_gap_zero_active s t k h (capVertex_strict i).admissible
        ha (capVertex_active i) hzi
      have hn := (contact_label_not_cap h (capVertex_strict i).admissible hc).2
      exact False.elim (hn (capVertex_label i))
  rcases h.selected with hA | hT | hcap
  · exact with_active_source a u A v h h' (Or.inl hA) hz
  · exact with_active_source a u A v h h' (Or.inr hT) hz
  · obtain ⟨i,hi⟩ := capWeights_some_pos h hcap
    have hsum := hz
    rw [cap_pair_first hcap] at hsum
    have hzi := zero_of_weighted_sum (capWeights_nonneg h hcap)
      (fun j => fixed_gap_nonneg s t k (capVertex_strict j).admissible h') hsum hi
    have hc := with_active_source (capVertex i).1 (capVertex i).2 A v
      (capVertex_strict i).admissible h' (capVertex_active i) hzi
    have hn := (contact_label_not_cap (capVertex_strict i).admissible h' hc).1
    exact False.elim (hn (capVertex_label i))

/-- The zero contacts have parallel geometric frames. The representative
relative frame is either 0 or pi/2; the axial radial coordinates remain free. -/
lemma contact_phase {a u A v : ℝ} {s t : TransverseSign}
    (h : Admissible a u) (h' : Admissible A v)
    (hc : OrderedContact a u A v s t) :
    relativePhase a u A v gap s t = 0 ∨
    relativePhase a u A v gap s t = Real.pi/2 := by
  rcases hc with ⟨rfl,rfl,ha,hb⟩ | ⟨rfl,ha,hb⟩ | ⟨rfl,ha,hb⟩
  · left
    rw [relativePhase,ha.1,ha.2,hb.1,hb.2,side_label]
    dsimp [gap,TransverseSign.coe]
    ring
  · right
    rw [relativePhase,ha.1,ha.2,side_label,axial_label h' hb]
    dsimp [gap,TransverseSign.coe]
    ring
  · right
    rw [relativePhase,hb.1,hb.2,side_label,axial_label h ha]
    dsimp [gap,TransverseSign.coe]
    ring

end Equality
end SquaresInCircles.Seven
