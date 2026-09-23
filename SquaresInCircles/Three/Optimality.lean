import SquaresInCircles.Three.Containing
import SquaresInCircles.Three.Construction

/-!
# The three-square optimum by occupied arcs

`Three.optimality` is the lower bound for arbitrary packings, with every square
rotated independently and an arbitrary disk centre.
`Three.optimality_and_attainment` adds the T of `Three/Construction.lean`,
which attains it.

A packing with `R^2 < 425/256` puts every square's centre strictly inside the
contact 16-gon (`p3_of_phi_lt`). `three_polygon_strict_impossible` refutes that
polygon relaxation, for whichever square contains the disk centre, by the
exterior case (`Three/Exterior.lean`) and the containing case
(`Three/Containing.lean`).
-/
noncomputable section
namespace SquaresInCircles

/-- No origin-containing branch is assumed or omitted: all three labels are handled. -/
theorem three_polygon_strict_impossible (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) : False := by
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      Disjoint {z | openSquare (S i) z} {z | openSquare (S j) z} := by
    rw [Set.disjoint_left]
    exact fun z hz hz' => hd i j hij z ⟨hz,hz'⟩
  obtain ⟨i,hi⟩ := three_exterior_reduction S o hd hp
  fin_cases i
  · exact three_containing_impossible (S 0) (S 1) (S 2) o
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
      (hp 0) (hp 1) (hp 2) hi
  · exact three_containing_impossible (S 1) (S 0) (S 2) o
      (hpair 1 0 (by decide)) (hpair 1 2 (by decide)) (hpair 0 2 (by decide))
      (hp 1) (hp 0) (hp 2) hi
  · exact three_containing_impossible (S 2) (S 0) (S 1) o
      (hpair 2 0 (by decide)) (hpair 2 1 (by decide)) (hpair 0 1 (by decide))
      (hp 2) (hp 0) (hp 1) hi

theorem Three.squared_lower (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (425:ℝ)/256 ≤ R^2 := by
  by_contra hn
  have hsmall : R^2 < (425:ℝ)/256 := lt_of_not_ge hn
  exact three_polygon_strict_impossible S o hp.disjoint
    (fun i => p3_of_phi_lt ((hp.phi_le i).trans_lt hsmall))

/-- The geometric lower bound; `Packing` carries no arc, tangent, or separator
assumption. -/
theorem Three.optimality (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Three.radius ≤ R :=
  radius_lower_of_squared hp.1
    (by rw [Three.radius_sq]; exact Three.squared_lower S o R hp)

theorem Three.optimality_and_attainment :
    (∀ (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → Three.radius ≤ R) ∧
    ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o Three.radius :=
  ⟨Three.optimality,Three.attainment⟩

end SquaresInCircles
