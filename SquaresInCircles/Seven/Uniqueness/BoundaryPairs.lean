import SquaresInCircles.Seven.Uniqueness.BoundaryGaps
import SquaresInCircles.Seven.Uniqueness.FixedGapEquality

/-!
# Boundary pair geometry

The original geometric non-overlap supplies an edge-normal separator. Its
support sum is nonnegative and can be zero only at a classified contact.
Both possible source frames and both marker orders are handled explicitly.
-/
noncomputable section
namespace SquaresInCircles.Seven.Equality

def CanonicalDisjoint (a u A v g : ℝ) (s t : TransverseSign) : Prop :=
  ∀ x y : ℝ, ¬ ((|x-a|<1/2 ∧ |y-s.coe*u|<1/2) ∧
    (|Real.cos (relativePhase a u A v g s t)*x+
        Real.sin (relativePhase a u A v g s t)*y-A|<1/2 ∧
     |-Real.sin (relativePhase a u A v g s t)*x+
        Real.cos (relativePhase a u A v g s t)*y-t.coe*v|<1/2))

lemma reverse_center_coordinates (a u A v g : ℝ) (s t : TransverseSign) :
    let d := relativePhase a u A v g s t
    Real.cos d*centerDX a u A v g s t+Real.sin d*centerDY a u A v g s t =
        -centerDX A v a u g t.flip s.flip ∧
    -Real.sin d*centerDX a u A v g s t+Real.cos d*centerDY a u A v g s t =
        centerDY A v a u g t.flip s.flip := by
  let d := relativePhase a u A v g s t
  have hu := Real.sin_sq_add_cos_sq d
  constructor <;> dsimp [centerDX,centerDY] <;>
    rw [reverse_reflected_phase,TransverseSign.coe_flip,TransverseSign.coe_flip]
  · change Real.cos d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
        Real.sin d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u)=_
    nlinarith [congrArg (fun x : ℝ => A*x) hu]
  · change -Real.sin d*(A*Real.cos d-t.coe*v*Real.sin d-a)+
        Real.cos d*(A*Real.sin d+t.coe*v*Real.cos d-s.coe*u)=_
    nlinarith [congrArg (fun x : ℝ => t.coe*v*x) hu]

private lemma first_axis_witness {a u A v g : ℝ} (s t : TransverseSign)
    (h : pairWidth (relativePhase a u A v g s t)≤|centerDX a u A v g s t| ∨
      pairWidth (relativePhase a u A v g s t)≤|centerDY a u A v g s t|) :
    ∃ k : Fin 4,pairSupport a u A v s t k g≤0 := by
  have he := pair_support_axis_values a u A v g s t
  rcases h with hx | hy
  · by_cases hdx : 0≤centerDX a u A v g s t
    · rw [abs_of_nonneg hdx] at hx
      exact ⟨0,by rw [he.1]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge hdx)] at hx
      exact ⟨2,by rw [he.2.2.1]; linarith⟩
  · by_cases hdy : 0≤centerDY a u A v g s t
    · rw [abs_of_nonneg hdy] at hy
      exact ⟨1,by rw [he.2.1]; linarith⟩
    · rw [abs_of_neg (lt_of_not_ge hdy)] at hy
      exact ⟨3,by rw [he.2.2.2]; linarith⟩

lemma canonical_separator {a u A v g : ℝ} (s t : TransverseSign)
    (hd : CanonicalDisjoint a u A v g s t) :
    (∃ k : Fin 4,pairSupport a u A v s t k g≤0) ∨
    (∃ k : Fin 4,pairSupport A v a u t.flip s.flip k g≤0) := by
  let d := relativePhase a u A v g s t
  let S := rotatedState a (s.coe*u) 0
  let T := rotatedState A (t.coe*v) d
  have hdisj : ∀p,¬(openSquare S p∧openSquare T p) := by
    intro p hp
    apply hd p.1 p.2
    have hSl := rotatedState_local a (s.coe*u) 0 p
    have hTl := rotatedState_local A (t.coe*v) d p
    change (|localX S p|<1/2 ∧ |localY S p|<1/2) ∧
      (|localX T p|<1/2 ∧ |localY T p|<1/2) at hp
    dsimp [S,T] at hp
    rw [hSl.1,hSl.2,hTl.1,hTl.2] at hp
    simpa only [Real.cos_zero,Real.sin_zero,one_mul,zero_mul,zero_add,add_zero,neg_zero] using hp
  have hrc : SAT.relativeCos S T=Real.cos d := by
    norm_num [SAT.relativeCos,S,T,rotatedState]
  have hrs : SAT.relativeSin S T=Real.sin d := by
    norm_num [SAT.relativeSin,S,T,rotatedState]
  have hwidth : SAT.threshold S T=pairWidth d := by
    rw [SAT.threshold,hrc,hrs]
    rfl
  have hdx : frameX S (sub T.center S.center)=centerDX a u A v g s t := by
    norm_num [frameX,S,T,rotatedState,sub,centerDX,d]
  have hdy : frameY S (sub T.center S.center)=centerDY a u A v g s t := by
    norm_num [frameY,S,T,rotatedState,sub,centerDY,d]
  have htx := SAT.relative_frameX S T (sub T.center S.center)
  have hty := SAT.relative_frameY S T (sub T.center S.center)
  rw [hrc,hrs,hdx,hdy] at htx hty
  have hsat := SAT.separating_axes S T hdisj
  rw [hwidth,hdx,hdy,←htx,←hty] at hsat
  have hr := reverse_center_coordinates a u A v g s t
  rcases hsat with hx | hy | hx | hy
  · exact Or.inl (first_axis_witness s t (Or.inl hx))
  · exact Or.inl (first_axis_witness s t (Or.inr hy))
  · rw [hr.1,abs_neg] at hx
    right
    apply first_axis_witness t.flip s.flip
    rw [reverse_reflected_phase]
    exact Or.inl hx
  · rw [hr.2] at hy
    right
    apply first_axis_witness t.flip s.flip
    rw [reverse_reflected_phase]
    exact Or.inr hy

lemma chart_disjoint_canonical {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) {g : ℝ}
    (hg : (g:Direction)=chartMarker D-chartMarker C)
    (hd : ∀p,¬(openSquare S p∧openSquare T p)) :
    CanonicalDisjoint C.a C.b D.a D.b g (chartSign C) (chartSign D) := by
  let d := relativePhase C.a C.b D.a D.b g (chartSign C) (chartSign D)
  have hphase : D.phase-C.phase=(d:Direction) := by
    have hh := hg
    rw [chartMarker_formula,chartMarker_formula] at hh
    dsimp [d,relativePhase]
    rw [Real.Angle.coe_sub,Real.Angle.coe_add]
    rw [hh]
    abel
  intro x y hxy
  apply hd (pointInDirection o C.phase x y)
  constructor
  · apply (C.cartesian x y).mpr
    rw [←chartSign_coordinate C]
    exact hxy.1
  · rw [pointInDirection_transition o C.phase D.phase x y]
    apply (D.cartesian _ _).mpr
    rw [hphase,Real.Angle.cos_coe,Real.Angle.sin_coe,←chartSign_coordinate D]
    exact hxy.2

lemma ordered_gap_not_lt {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Admissible C.a C.b) (hD : Admissible D.a D.b)
    {g : ℝ} (hg0 : 0≤g) (hg : (g:Direction)=chartMarker D-chartMarker C)
    (hd : ∀p,¬(openSquare S p∧openSquare T p)) : ¬g<gap := by
  intro hsmall
  rcases canonical_separator (chartSign C) (chartSign D)
    (chart_disjoint_canonical C D hg hd) with ⟨k,hk⟩ | ⟨k,hk⟩
  · exact (not_le_of_gt (all_gap_support_pos_below (chartSign C) (chartSign D) k
      hC hD ⟨hg0,hsmall⟩)) hk
  · exact (not_le_of_gt (all_gap_support_pos_below (chartSign D).flip (chartSign C).flip k
      hD hC ⟨hg0,hsmall⟩)) hk

/-- Weak marker separation at the exact candidate radius. -/
theorem marker_separation_closed {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Admissible C.a C.b) (hD : Admissible D.a D.b)
    (hd : ∀p,¬(openSquare S p∧openSquare T p)) :
    gap≤dist (chartMarker C) (chartMarker D) := by
  let d : ℝ := (chartMarker D-chartMarker C).toReal
  have hdist : dist (chartMarker C) (chartMarker D)=|d| := by
    rw [dist_comm,direction_dist]
    rfl
  have he : (d:Direction)=chartMarker D-chartMarker C := Real.Angle.coe_toReal _
  rw [hdist]
  by_cases hd0 : 0≤d
  · rw [abs_of_nonneg hd0]
    exact le_of_not_gt (ordered_gap_not_lt C D hC hD hd0 he hd)
  · rw [abs_of_neg (lt_of_not_ge hd0)]
    have he' : ((-d:ℝ):Direction)=chartMarker C-chartMarker D := by
      rw [Real.Angle.coe_neg,he]
      abel
    exact le_of_not_gt (ordered_gap_not_lt D C hD hC (by linarith) he'
      (fun p hp => hd p ⟨hp.2,hp.1⟩))

/-- The equality theorem is directed: the order is part of the angular equation. -/
theorem ordered_marker_contact {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : Admissible C.a C.b) (hD : Admissible D.a D.b)
    (he : (gap:Direction)=chartMarker D-chartMarker C)
    (hd : ∀p,¬(openSquare S p∧openSquare T p)) :
    OrderedContact C.a C.b D.a D.b (chartSign C) (chartSign D) := by
  rcases canonical_separator (chartSign C) (chartSign D)
    (chart_disjoint_canonical C D he hd) with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hz := le_antisymm hk (fixed_gap_nonneg (chartSign C) (chartSign D) k hC hD)
    exact fixed_gap_zero (chartSign C) (chartSign D) k hC hD hz
  · have hz := le_antisymm hk
      (fixed_gap_nonneg (chartSign D).flip (chartSign C).flip k hD hC)
    exact reflected_reverse_contact
      (fixed_gap_zero (chartSign D).flip (chartSign C).flip k hD hC hz)

end SquaresInCircles.Seven.Equality
