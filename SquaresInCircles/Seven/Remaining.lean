import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Seven.MarkerArc

/-!
# Exact statements for the remaining analytical formalization

The full canonical marker-arc theorem is now supplied. The fixed-gap support
partition and the geometric reduction below are still proposition definitions,
not asserted theorems. The final lower bound remains conditional.
-/
noncomputable section
namespace SquaresInCircles.Seven

inductive TransverseSign where
  | positive
  | negative
  deriving DecidableEq, Fintype

def TransverseSign.coe : TransverseSign → ℝ
  | .positive => 1
  | .negative => -1

def cardinalAngle (k : Fin 4) : ℝ := (k.val : ℝ)*Real.pi/2

/-- Actual support sum when the affine marker gap is `gamma`. -/
def pairSupport (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4) (gamma : ℝ) : ℝ :=
  support a (s.coe*u) (cardinalAngle k) +
  support A (t.coe*v)
    (cardinalAngle k+Real.pi-gamma-s.coe*label a u+t.coe*label A v)

/-- Closed membership is intentional; tangencies need not be interior. -/
def MarkerArcStatement : Prop :=
  ∀ (a u t : ℝ), Admissible a u →
    |t-label a u| ≤ 801/1600 →
    |Real.cos t-a| ≤ 1/2 ∧ |Real.sin t-u| ≤ 1/2

/-- Full marker-arc proof, rather than just marker-point membership. -/
theorem markerArc_proved : MarkerArcStatement := by
  intro a u t h ht
  exact marker_arc h ht

/-- All fixed-gap source/sign/label sectors, with the strictness needed below
the candidate. The new source proves only some sectors of this proposition. -/
def FixedGapStatement : Prop :=
  ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
    Admissible a u → Admissible A v →
    0 ≤ pairSupport a u A v s t k gap ∧
    (StrictlyAdmissible a u → StrictlyAdmissible A v →
      0 < pairSupport a u A v s t k gap)

/-- Intermediate-angle minimization and transport through square charts.
This implication has not been proved in this extension. -/
def GeometricReductionStatement : Prop :=
  MarkerArcStatement → FixedGapStatement → MarkerSeparationStatement

theorem optimality_of_analytic_obligations
    (hsupport : FixedGapStatement)
    (hgeometry : GeometricReductionStatement)
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    radius ≤ R :=
  optimality_of_marker_separation (hgeometry markerArc_proved hsupport) S o R hp

end SquaresInCircles.Seven
