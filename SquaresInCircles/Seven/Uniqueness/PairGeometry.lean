import SquaresInCircles.Seven.Uniqueness.ClosedGaps
import SquaresInCircles.Seven.Uniqueness.FixedGapEquality
import SquaresInCircles.Seven.MarkerSeparation

/-!
# Contacts of actual squares

Disjoint exterior squares with closed containment have markers at least `π/3`
apart, and at exactly `π/3` their states form a contact: a separating axis
gives a nonpositive support sum.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

def CanonicalDisjoint (a u A v g : ℝ) (s t : TransverseSign) : Prop :=
  ∀ x y : ℝ, ¬ ((|x-a| < 1/2 ∧ |y-s.coe*u| < 1/2) ∧
    (|Real.cos (relativePhase a u A v g s t)*x+
       Real.sin (relativePhase a u A v g s t)*y-A| < 1/2 ∧
     |-Real.sin (relativePhase a u A v g s t)*x+
       Real.cos (relativePhase a u A v g s t)*y-t.coe*v| < 1/2))

private lemma first_axes_of_support {a u A v g : ℝ} (s t : TransverseSign)
    (h : ∀ k, 0 < pairSupport a u A v s t k g) :
    |centerDX a u A v g s t| < pairWidth (relativePhase a u A v g s t) ∧
    |centerDY a u A v g s t| < pairWidth (relativePhase a u A v g s t) := by
  have he := pair_support_axis_values a u A v g s t
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rw [he.1] at h0
  rw [he.2.1] at h1
  rw [he.2.2.1] at h2
  rw [he.2.2.2] at h3
  exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,
    abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma reverse_center_coordinates (a u A v g : ℝ) (s t : TransverseSign) :
    Real.cos (relativePhase a u A v g s t)*centerDX a u A v g s t+
      Real.sin (relativePhase a u A v g s t)*centerDY a u A v g s t =
        -centerDX A v a u g t.flip s.flip ∧
    -Real.sin (relativePhase a u A v g s t)*centerDX a u A v g s t+
      Real.cos (relativePhase a u A v g s t)*centerDY a u A v g s t =
        centerDY A v a u g t.flip s.flip := by
  let d := relativePhase a u A v g s t
  have hu := Real.sin_sq_add_cos_sq d
  constructor <;> dsimp [centerDX,centerDY] <;>
    rw [reverse_reflected_phase] <;> simp only [TransverseSign.coe_flip]
  · change Real.cos d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.sin d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u) = _
    nlinarith [congrArg (fun z : ℝ => A*z) hu]
  · change -Real.sin d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
      Real.cos d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u) = _
    nlinarith [congrArg (fun z : ℝ => t.coe*v*z) hu]

/-- A disjoint canonical pair has a nonpositive support in one of its frames. -/
lemma canonical_has_separator {a u A v g : ℝ} (s t : TransverseSign)
    (hd : CanonicalDisjoint a u A v g s t) :
    (∃ k, pairSupport a u A v s t k g ≤ 0) ∨
    (∃ k, pairSupport A v a u t.flip s.flip k g ≤ 0) := by
  by_contra hn
  have hf : ∀ k, 0 < pairSupport a u A v s t k g := by
    intro k
    by_contra hk
    exact hn (Or.inl ⟨k,le_of_not_gt hk⟩)
  have hr : ∀ k, 0 < pairSupport A v a u t.flip s.flip k g := by
    intro k
    by_contra hk
    exact hn (Or.inr ⟨k,le_of_not_gt hk⟩)
  have hfirst := first_axes_of_support s t hf
  have hsecond := first_axes_of_support t.flip s.flip hr
  rw [reverse_reflected_phase] at hsecond
  let d := relativePhase a u A v g s t
  let S := rotatedState a (s.coe*u) 0
  let T := rotatedState A (t.coe*v) d
  have hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p) := by
    intro p hp
    have hS := rotatedState_local a (s.coe*u) 0 p
    have hT := rotatedState_local A (t.coe*v) d p
    apply hd p.1 p.2
    constructor
    · have hh := hp.1
      change |localX S p| < 1/2 ∧ |localY S p| < 1/2 at hh
      dsimp [S] at hh
      rw [hS.1,hS.2] at hh
      simpa using hh
    · have hh := hp.2
      change |localX T p| < 1/2 ∧ |localY T p| < 1/2 at hh
      dsimp [T] at hh
      rw [hT.1,hT.2] at hh
      exact hh
  have hc : SAT.relativeCos S T = Real.cos d := by
    norm_num [S,T,rotatedState,SAT.relativeCos]
  have hs : SAT.relativeSin S T = Real.sin d := by
    norm_num [S,T,rotatedState,SAT.relativeSin]
  have hw : SAT.threshold S T = pairWidth d := by rw [SAT.threshold,hc,hs]; rfl
  have hx : frameX S (sub T.center S.center) = centerDX a u A v g s t := by
    norm_num [S,T,rotatedState,frameX,sub,centerDX,d]
  have hy : frameY S (sub T.center S.center) = centerDY a u A v g s t := by
    norm_num [S,T,rotatedState,frameY,sub,centerDY,d]
  have htx := SAT.relative_frameX S T (sub T.center S.center)
  have hty := SAT.relative_frameY S T (sub T.center S.center)
  rw [hc,hs,hx,hy] at htx hty
  have he := reverse_center_coordinates a u A v g s t
  have hsep := SAT.separating_axes S T hdisj
  rw [hw,hx,hy,←htx,←hty,he.1,he.2,abs_neg] at hsep
  rcases hsep with hsep | hsep | hsep | hsep
  · exact (not_le_of_gt hfirst.1) hsep
  · exact (not_le_of_gt hfirst.2) hsep
  · exact (not_le_of_gt hsecond.1) hsep
  · exact (not_le_of_gt hsecond.2) hsep

lemma charts_disjoint_canonical {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) {g : ℝ}
    (hang : (g : Direction) = chartMarker D-chartMarker C)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    CanonicalDisjoint C.a C.b D.a D.b g (chartSign C) (chartSign D) := by
  let d := relativePhase C.a C.b D.a D.b g (chartSign C) (chartSign D)
  have hphase : D.phase-C.phase = (d : Direction) := by
    rw [chartMarker_formula,chartMarker_formula] at hang
    have he : (g : Direction)+(((chartSign C).coe*label C.a C.b : ℝ) : Direction)-
        (((chartSign D).coe*label D.a D.b : ℝ) : Direction) = D.phase-C.phase := by
      rw [hang]
      abel
    simpa only [d,relativePhase,Real.Angle.coe_add,Real.Angle.coe_sub] using he.symm
  intro x y hp
  apply hd (pointInDirection o C.phase x y)
  constructor
  · apply (C.cartesian x y).mpr
    rw [←chartSign_coordinate C]
    exact hp.1
  · rw [pointInDirection_transition o C.phase D.phase x y]
    apply (D.cartesian _ _).mpr
    rw [hphase,Real.Angle.cos_coe,Real.Angle.sin_coe,←chartSign_coordinate D]
    exact hp.2

lemma ordered_gap_not_below {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Admissible C.a C.b) (hD : Admissible D.a D.b)
    {g : ℝ} (hg : 0 ≤ g ∧ g < gap)
    (hang : (g : Direction) = chartMarker D-chartMarker C)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) : False := by
  have hcan := charts_disjoint_canonical C D hang hd
  rcases canonical_has_separator (chartSign C) (chartSign D) hcan with ⟨k,hk⟩ | ⟨k,hk⟩
  · exact (not_le_of_gt (all_gap_pos_below (chartSign C) (chartSign D) k hC hD hg)) hk
  · exact (not_le_of_gt (all_gap_pos_below (chartSign D).flip (chartSign C).flip k hD hC hg)) hk

/-- The pair theorem at the optimal radius: disjoint exterior squares with
admissible states have markers at least `π/3` apart. -/
theorem marker_separation_closed {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Admissible C.a C.b) (hD : Admissible D.a D.b)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    gap ≤ dist (chartMarker C) (chartMarker D) := by
  by_contra hn
  have hdist : dist (chartMarker C) (chartMarker D) < gap := lt_of_not_ge hn
  let g := (chartMarker D-chartMarker C).toReal
  have hg : |g| < gap := by
    have he : dist (chartMarker C) (chartMarker D) = |g| := by
      rw [dist_comm,direction_dist]
    rwa [he] at hdist
  have hang : (g : Direction) = chartMarker D-chartMarker C := Real.Angle.coe_toReal _
  by_cases hpos : 0 ≤ g
  · exact ordered_gap_not_below C D hC hD
      ⟨hpos,by simpa [abs_of_nonneg hpos] using hg⟩ hang hd
  · have hrev : ((-g : ℝ) : Direction) = chartMarker C-chartMarker D := by
      rw [Real.Angle.coe_neg,hang]
      abel
    exact ordered_gap_not_below D C hD hC
      ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hpos)] using hg⟩ hrev
      (fun p hp => hd p ⟨hp.2,hp.1⟩)

/-- Disjoint exterior squares with admissible states, the marker of `D`
exactly `π/3` ahead of that of `C`, are a contact. -/
theorem ordered_chart_contact {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Admissible C.a C.b) (hD : Admissible D.a D.b)
    (hang : (gap : Direction) = chartMarker D-chartMarker C)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    OrderedContact C.a C.b D.a D.b (chartSign C) (chartSign D) := by
  have hcan := charts_disjoint_canonical C D hang hd
  rcases canonical_has_separator (chartSign C) (chartSign D) hcan with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hz := le_antisymm hk (fixed_gap_nonneg (chartSign C) (chartSign D) k hC hD)
    exact fixed_gap_zero (chartSign C) (chartSign D) k hC hD hz
  · have hz := le_antisymm hk (fixed_gap_nonneg (chartSign D).flip (chartSign C).flip k hD hC)
    exact reflected_reverse_contact
      (fixed_gap_zero (chartSign D).flip (chartSign C).flip k hD hC hz)

end Equality
end SquaresInCircles.Seven
