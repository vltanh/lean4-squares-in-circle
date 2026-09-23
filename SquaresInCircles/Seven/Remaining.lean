import SquaresInCircles.Seven.Reduction
import SquaresInCircles.Seven.Support

/-!
# Exact statements for the remaining analytical formalization

The declarations in this file are proposition DEFINITIONS, not theorems.
Nothing in this file asserts that the conditions hold. The statements are
included so that the remaining proof work has an unambiguous interface.
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

/-- The manuscript's genuine marker-arc assertion. Closed membership is
intentional: tangent boundary points cannot be assumed to be interior. -/
def MarkerArcStatement : Prop :=
  ∀ (a u t : ℝ), Admissible a u →
    |t-label a u| ≤ 801/1600 →
    |Real.cos t-a| ≤ 1/2 ∧ |Real.sin t-u| ≤ 1/2

/-- All fixed-gap source/sign/label sectors, with the strictness needed below
the candidate. The new source proves only some sectors of this proposition. -/
def FixedGapStatement : Prop :=
  ∀ (a u A v : ℝ) (s t : TransverseSign) (k : Fin 4),
    Admissible a u → Admissible A v →
    0 ≤ pairSupport a u A v s t k gap ∧
    (StrictlyAdmissible a u → StrictlyAdmissible A v →
      0 < pairSupport a u A v s t k gap)

/-- The intermediate-angle minimum argument and its transport through the
square charts. This implication has not been proved in this extension. -/
def GeometricReductionStatement : Prop :=
  MarkerArcStatement → FixedGapStatement → MarkerSeparationStatement

/-- Once the three separately stated obligations are supplied, the finished
counting/selection layer assembles them without an additional packing axiom. -/
theorem optimality_of_analytic_obligations
    (harc : MarkerArcStatement) (hsupport : FixedGapStatement)
    (hgeometry : GeometricReductionStatement)
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) :
    radius ≤ R :=
  optimality_of_marker_separation (hgeometry harc hsupport) S o R hp

end SquaresInCircles.Seven
