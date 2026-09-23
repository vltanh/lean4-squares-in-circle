import SquaresInCircles.Five.Containing
import SquaresInCircles.Common.Regions
import SquaresInCircles.Five.Construction

/-! Five squares: dodecagon tangents, occupied arcs, and a safe central sweep. -/
noncomputable section
open Set
namespace SquaresInCircles

lemma fin_five_other (i : Fin 5) : ∃ j : Fin 5, i ≠ j := by
  by_cases hi : i=0
  · exact ⟨1,by simp [hi]⟩
  · exact ⟨0,hi⟩

/-- The strict tangent relaxation itself is impossible; no circle is assumed here. -/
theorem five_polygon_strict_impossible (S : Fin 5 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P5Strict (alpha (S i) o) (beta (S i) o)) : False := by
  classical
  have hweak (i : Fin 5) := p5Strict_to_p5 (hp i)
  have hext : ∀ i : Fin 5, ∃ A : OpenArc o auxFive (rayRegions S o i),
      Real.pi/5 ≤ A.halfWidth ∧
        (¬ openSquare (S i) o → Real.pi/5 < A.halfWidth) := by
    intro i
    by_cases hi : openSquare (S i) o
    · obtain ⟨j,hij⟩ := fin_five_other i
      have hne := center_ne_of_strict_octagons (S i) (S j) o
        (hd i j hij) (hp i).1 (hp j).1
      obtain ⟨A,hA⟩ := five_containing_arc (S i) o hi hne
      rw [rayRegions_pos hi]
      exact ⟨A,by rw [hA],fun hn => False.elim (hn hi)⟩
    · obtain ⟨A,hA⟩ := five_exterior_arc (S i) o (hweak i) hi
      rw [rayRegions_neg hi]
      exact ⟨A,hA.le,fun _ => hA⟩
  choose A hA hstrict using hext
  have hout : ∃ i : Fin 5, ¬ openSquare (S i) o := by
    by_contra hn
    push Not at hn
    exact hd 0 1 (by decide) o ⟨hn 0,hn 1⟩
  apply uniform_arc_excess (n := 5) (by decide) A
    (rayRegions_disjoint hd (fun i => (hweak i).1)) hA
  obtain ⟨i,hi⟩ := hout
  exact ⟨i,hstrict i hi⟩

theorem five_squared_lower (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (5:ℝ)/2 ≤ R^2 := by
  by_contra hn
  exact five_polygon_strict_impossible S o hp.disjoint
    (fun i => p5_of_phi_lt ((hp.phi_le i).trans_lt (lt_of_not_ge hn)))

theorem Five.optimality (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Five.radius ≤ R :=
  radius_lower_of_squared hp.1
    (by rw [Five.radius_sq]; exact five_squared_lower S o R hp)

theorem Five.optimality_and_attainment :
    (∀ (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → Five.radius ≤ R) ∧
    ∃ (S : Fin 5 → UnitSquare) (o : Point), Packing S o Five.radius :=
  ⟨Five.optimality,Five.attainment⟩

end SquaresInCircles
