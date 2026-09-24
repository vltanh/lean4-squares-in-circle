import SquaresInCircles.Seven.CanonicalPair
import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Common.Coordinates

/-!
# Marker separation for the original square model

Each reflected chart is represented by a positively oriented frame and a
signed transverse coordinate. The circle's toReal difference selects the
positive marker order; swapping charts handles the other sign. No additional
orientation, generic-position, or arc-order hypothesis enters the theorem.
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

/-- Ordered chart pair: sufficiently close markers give a common open-square
point. This is a theorem about actual points in the repository's geometry. -/
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

/-- Unconditional strict pair theorem. The square frames and translations are
arbitrary; the only geometric hypotheses are the original containments,
exteriority, and disjoint open interiors. -/
theorem marker_separation : MarkerSeparationStatement := by
  intro S T o C D hsortC hsortD hextC hextD hphiC hphiD hdisj
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
