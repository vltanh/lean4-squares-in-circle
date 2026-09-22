import ThreeUnitSquaresInCircle.ForbiddenChain
import ThreeUnitSquaresInCircle.CoefficientBridge
import ThreeUnitSquaresInCircle.Construction

/-!
# End-to-end proof

`optimality` states the lower bound directly, with no intermediate abbreviation:
there are no `sorry` terms, no custom `axiom` declarations, and no
`native_decide`. `AxiomAudit.lean` reports that it depends only on `propext`,
`Classical.choice` and `Quot.sound`.

`Packing` is the plain geometric predicate: nonnegative radius, every closed
square inside the disk, and pairwise disjoint open interiors. It carries no
certificate-existence, orientation, or lower-bound assumption.

The argument runs as follows. `normalize_orientations` replaces an arbitrary
packing with a rigidly equivalent one whose angle pair lies in the domain
triangle; `choose_separating_axes` supplies signed edge normals from the
disjoint open interiors; `forbidden_chain` rules out the cardinal patterns
containing a directed chain; `Combinatorics.classification` leaves six patterns,
hence 48 branches; `select_certificate` picks one of the 53 rational
certificates whose polygon contains the angle pair and yields the real lower
bound; and `table_dual_bound` supplies the matching upper bound. Together these
contradict `R^2 < targetSq`.

Status: compiles against Lean 4.34.0 / mathlib v4.34.0.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Cert
open RatData

theorem optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : optimalRadius ≤ R := by
  apply radius_lower_of_squared hp.1
  by_contra hnot
  have hsmall : R^2 < targetSq := lt_of_not_ge hnot
  obtain ⟨c,x,hx,hp0⟩ := normalize_orientations S o R hp
  obtain ⟨c',k,s,hp1,hk0,hs,hsep⟩ := choose_separating_axes c x R hx hp0
  have hchain := forbidden_chain c' x R hx hp1 hsmall k s hk0 hs hsep
  have hk : (k 1,k 2) ∈ Combinatorics.remaining :=
    (Combinatorics.classification (k 1) (k 2)).mp hchain
  obtain ⟨i,hik,his,hvalue⟩ := select_certificate k s hk0 hk hs x hx
  have hdual : polynomial (table i) x ≤ R^2 := by
    apply table_dual_bound i x c' R hp1
    simpa only [hik,his] using hsep
  exact (not_le_of_gt hsmall) (hvalue.trans hdual)

/-- The global bound together with the explicit attaining construction. -/
theorem optimality_and_attainment :
    (∀ (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ),
        Packing S o R → optimalRadius ≤ R) ∧
      ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o optimalRadius :=
  ⟨optimality, exists_packing_at_optimum⟩

end ThreeUnitSquaresInCircle.Cert
