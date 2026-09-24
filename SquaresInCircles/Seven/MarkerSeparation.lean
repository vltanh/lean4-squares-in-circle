import SquaresInCircles.Seven.CanonicalPair
import SquaresInCircles.Common.Coordinates

/-!
# The pair theorem for actual squares

Two disjoint squares that avoid the disk centre, each in the disk of squared
radius below `13/4`, have markers more than `π/3` apart. A chart with a
reversed orientation is read as a turned frame with a signed transverse
coordinate, so each square sits at its state in the frame of its phase and the
pair is a canonical pair. The sign of the marker difference decides which
square plays the first role.
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

/-- If the marker of `D` is `g ∈ [0, π/3]` ahead of the marker of `C`, and both
states are strictly admissible, the open squares meet. -/
theorem close_ordered_charts_overlap {S T : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hC : StrictlyAdmissible C.a C.b) (hD : StrictlyAdmissible D.a D.b)
    {g : ℝ} (hg : 0≤g ∧ g≤gap)
    (hangle : (g:Direction)=chartMarker D-chartMarker C) :
    ∃p,openSquare S p ∧ openSquare T p := by
  let s := chartSign C
  let t := chartSign D
  let d := relativePhase C.a C.b D.a D.b g s t
  have hphase : D.phase-C.phase=(d:Direction) := by
    have h := hangle
    rw [chartMarker_formula,chartMarker_formula] at h
    have he : (g:Direction)+((s.coe*label C.a C.b:ℝ):Direction)-
        ((t.coe*label D.a D.b:ℝ):Direction)=D.phase-C.phase := by
      change (g:Direction)+(((chartSign C).coe*label C.a C.b:ℝ):Direction)-
        (((chartSign D).coe*label D.a D.b:ℝ):Direction)=_
      rw [h]
      abel
    simpa only [d,relativePhase,Real.Angle.coe_add,Real.Angle.coe_sub] using he.symm
  obtain ⟨x,y,hxy,hxy'⟩ := canonical_pair_overlap s t hC hD hg
  refine ⟨pointInDirection o C.phase x y,?_,?_⟩
  · apply (C.cartesian x y).mpr
    rw [←chartSign_coordinate C]
    exact hxy
  · rw [pointInDirection_transition o C.phase D.phase x y]
    apply (D.cartesian _ _).mpr
    rw [hphase,Real.Angle.cos_coe,Real.Angle.sin_coe,←chartSign_coordinate D]
    exact hxy'

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
  by_contra hn
  have hdist : dist (chartMarker C) (chartMarker D)≤gap := le_of_not_gt hn
  let d : ℝ := (chartMarker D-chartMarker C).toReal
  have hdabs : |d|≤gap := by
    have he : dist (chartMarker C) (chartMarker D)=|d| := by
      rw [dist_comm,direction_dist]
    simpa only [he] using hdist
  have hdangle : (d:Direction)=chartMarker D-chartMarker C :=
    Real.Angle.coe_toReal _
  by_cases hd : 0≤d
  · have hdu : d≤gap := by rw [abs_of_nonneg hd] at hdabs; exact hdabs
    obtain ⟨p,hp,hp'⟩ := close_ordered_charts_overlap C D hC hD ⟨hd,hdu⟩ hdangle
    exact hdisj p ⟨hp,hp'⟩
  · have hd' : 0≤-d := by linarith
    have hdu : -d≤gap := by rw [abs_of_neg (lt_of_not_ge hd)] at hdabs; exact hdabs
    have hang : ((-d:ℝ):Direction)=chartMarker C-chartMarker D := by
      rw [Real.Angle.coe_neg,hdangle]
      abel
    obtain ⟨p,hp,hp'⟩ := close_ordered_charts_overlap D C hD hC ⟨hd',hdu⟩ hang
    exact hdisj p ⟨hp',hp⟩

end SquaresInCircles.Seven
