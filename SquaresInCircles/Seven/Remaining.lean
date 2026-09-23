import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Seven.EasySectors

/-!
# Exact remaining proof obligations

The canonical marker-arc theorem has a proof body, as do the whole-domain
outward, backward and inward-negative support sectors. The rest of the support
partition and the geometric reduction are not asserted here as theorems.
-/
noncomputable section
namespace SquaresInCircles.Seven

def MarkerArcStatement : Prop :=
  ∀ (a u t : ℝ), Admissible a u →
    |t-label a u| ≤ 801/1600 →
    |Real.cos t-a| ≤ 1/2 ∧ |Real.sin t-u| ≤ 1/2

theorem markerArc_proved : MarkerArcStatement := by
  intro a u t h ht
  exact marker_arc h ht

/-- All fixed-gap sectors, including strictness. Only a subset is proved so far. -/
def FixedGapStatement : Prop :=
  ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
    Admissible a u → Admissible A v →
    0 ≤ pairSupport a u A v s t k gap ∧
    (StrictlyAdmissible a u → StrictlyAdmissible A v →
      0 < pairSupport a u A v s t k gap)

/-- Intermediate-angle minimization, separating axes and chart transport. -/
def GeometricReductionStatement : Prop :=
  MarkerArcStatement → FixedGapStatement → MarkerSeparationStatement

theorem optimality_of_analytic_obligations
    (hsupport : FixedGapStatement)
    (hgeometry : GeometricReductionStatement)
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    radius ≤ R :=
  optimality_of_marker_separation (hgeometry markerArc_proved hsupport) S o R hp

end SquaresInCircles.Seven
