import SquaresInCircles.Seven.Optimality

/-!
# Former proof obligations, now supplied by explicit proof chains

The proposition names are retained for compatibility with the early draft.
They are no longer unproved inputs to the public lower-bound theorem.
`Seven.optimality` and `Seven.optimality_and_attainment` are unconditional.

None of this is a claim that the new source has been compiled.
-/
noncomputable section
namespace SquaresInCircles.Seven

def MarkerArcStatement : Prop :=
  ∀(a u t : ℝ),Admissible a u →
    |t-label a u|≤801/1600 →
    |Real.cos t-a|≤1/2 ∧ |Real.sin t-u|≤1/2

theorem markerArc_proved : MarkerArcStatement := by
  intro a u t h ht
  exact marker_arc h ht

def FixedGapStatement : Prop :=
  ∀(a u A v : ℝ)(s t : TransverseSign)(k : Fin 4),
    Admissible a u → Admissible A v →
    0≤pairSupport a u A v s t k gap ∧
    (StrictlyAdmissible a u → StrictlyAdmissible A v →
      0<pairSupport a u A v s t k gap)

theorem fixedGap_proved : FixedGapStatement := by
  intro a u A v s t k h h'
  exact fixed_gap_property a u A v s t k h h'

/-- The historical implication is weaker than the unconditional pair theorem
now supplied by `MarkerSeparation.lean`. It is retained as a compatibility API. -/
def GeometricReductionStatement : Prop :=
  MarkerArcStatement → FixedGapStatement → MarkerSeparationStatement

theorem geometricReduction_proved : GeometricReductionStatement := by
  intro _ _
  exact marker_separation

/-- All three formerly external proof obligations have proof terms. -/
theorem analytic_obligations_proved :
    MarkerArcStatement ∧ FixedGapStatement ∧ GeometricReductionStatement :=
  ⟨markerArc_proved,fixedGap_proved,geometricReduction_proved⟩

/-- Backwards-compatible conditional wrapper; the hypotheses are no longer
needed to invoke the unconditional public theorem. -/
theorem optimality_of_analytic_obligations
    (_hsupport : FixedGapStatement) (_hgeometry : GeometricReductionStatement)
    (S : Fin 7 → UnitSquare) (o : Point) (R : ℝ) (hp : Packing S o R) : radius≤R :=
  optimality S o R hp

end SquaresInCircles.Seven
