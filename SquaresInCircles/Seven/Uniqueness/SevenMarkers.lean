import SquaresInCircles.Seven.MarkerSeparation

/-!
# Seven markers

Seven directions cannot be pairwise at least `π/3` apart, since closed arcs of
half-width `1/2` about them would be disjoint. So at the optimal radius the
markers of seven exterior squares are impossible, and some square contains the
disk centre.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

/-- Seven directions cannot be pairwise at least `π/3` apart. -/
lemma seven_directions_impossible (c : Fin 7 → Direction)
    (hsep : ∀ i j, i ≠ j → gap ≤ dist (c i) (c j)) : False := by
  have hballs : Pairwise (fun i j =>
      Disjoint (Metric.closedBall (c i) (1/2)) (Metric.closedBall (c j) (1/2))) := by
    intro i j hij
    apply Metric.closedBall_disjoint_closedBall
    have hg := hsep i j hij
    dsimp [gap] at hg
    linarith [pi_lower_157]
  have hb := closed_arc_budget c (fun _ => (1/2 : ℝ))
    (fun _ => ⟨by norm_num,by linarith [Real.pi_pos,pi_lower_157]⟩) hballs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  norm_num at hb
  linarith [pi_lt_22_over_7]

/-- At the optimal radius some square contains the disk centre. -/
theorem exists_containing (S : Fin 7 → UnitSquare) (o : Point)
    (hp : Packing S o radius) : ∃ i, openSquare (S i) o := by
  classical
  by_contra hn
  have hext : ∀ i, ¬ openSquare (S i) o := by simpa only [not_exists] using hn
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hadm (i : Fin 7) : Admissible (C i).a (C i).b := by
    apply chart_admissible (C i) (hsort i) (hext i)
    have hh := hp.phi_le i
    simpa only [radius_sq,targetSq] using hh
  apply seven_directions_impossible (fun i => chartMarker (C i))
  intro i j hij
  exact marker_separation_closed (C i) (C j) (hadm i) (hadm j) (hp.disjoint i j hij)

end Equality
end SquaresInCircles.Seven
