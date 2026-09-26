import SquaresInCircles.Seven.CanonicalPair
import SquaresInCircles.Seven.AllGaps
import SquaresInCircles.Common.Coordinates

/-!
# The pair theorem for actual squares

Two disjoint squares that avoid the disk centre, each in the disk of squared
radius `13/4`, have markers at least `π/3` apart, and at exactly `π/3` their
states form a contact. A chart with a reversed orientation is read as a turned
frame with a signed transverse coordinate, so each square sits at its state in
the frame of its phase and the pair is a canonical pair; a separating axis
gives a nonpositive support sum. The sign of the marker difference decides
which square plays the first role. Inside the disk of squared radius below
`13/4` no contact is possible, so the markers are more than `π/3` apart.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- Reversal in a square chart is recorded as the sign of its center's second
coordinate; the represented geometric square is unchanged. -/
def chartSign {S : UnitSquare} {o : Point} (C : SquareChart S o) : TransverseSign :=
  if C.reversed then .negative else .positive

lemma chartSign_coordinate {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    (chartSign C).coe*C.b=C.signedB := by
  cases h : C.reversed <;>
    simp [chartSign,h,SquareChart.signedB,TransverseSign.coe]

lemma chartMarker_formula {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    chartMarker C=C.phase+(((chartSign C).coe*label C.a C.b:ℝ):Direction) := by
  cases h : C.reversed <;>
    simp [chartMarker,chartAngle,chartSign,h,TransverseSign.coe]

namespace Equality

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

/-- The pair theorem: disjoint exterior squares in a disk of squared radius
below `13/4` have markers more than `π/3` apart. The frames and positions of
the squares are arbitrary. -/
theorem marker_separation {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hsortC : C.b ≤ C.a) (hsortD : D.b ≤ D.a)
    (hextC : ¬ openSquare S o) (hextD : ¬ openSquare T o)
    (hphiC : phi (alpha S o) (beta S o) < targetSq)
    (hphiD : phi (alpha T o) (beta T o) < targetSq)
    (hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    gap < dist (chartMarker C) (chartMarker D) := by
  have hC := chart_strictlyAdmissible C hsortC hextC hphiC
  have hD := chart_strictlyAdmissible D hsortD hextD hphiD
  refine (Equality.marker_separation_closed C D hC.admissible hD.admissible hdisj).lt_of_ne
    fun heq => ?_
  let d : ℝ := (chartMarker D-chartMarker C).toReal
  have hdangle : (d:Direction)=chartMarker D-chartMarker C := Real.Angle.coe_toReal _
  have hdabs : |d|=gap := by rw [heq,dist_comm,direction_dist]
  by_cases hd : 0≤d
  · rw [abs_of_nonneg hd] at hdabs
    rw [hdabs] at hdangle
    exact Equality.contact_not_strict
      (Equality.ordered_chart_contact C D hC.admissible hD.admissible hdangle hdisj) hC hD
  · rw [abs_of_neg (lt_of_not_ge hd)] at hdabs
    have hang : (gap:Direction)=chartMarker C-chartMarker D := by
      rw [← hdabs,Real.Angle.coe_neg,hdangle]
      abel
    exact Equality.contact_not_strict (Equality.ordered_chart_contact D C hD.admissible
      hC.admissible hang (fun p hp => hdisj p ⟨hp.2,hp.1⟩)) hD hC

end SquaresInCircles.Seven
