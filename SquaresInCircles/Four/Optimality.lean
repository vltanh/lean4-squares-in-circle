import SquaresInCircles.Four.Containing
import SquaresInCircles.Four.Tangents
import SquaresInCircles.Common.Regions
import SquaresInCircles.Four.Construction

/-! Four squares: strict diamond constraints, a common slightly shrunken
auxiliary circle, and the same disjoint-region angular budget as for five. -/
noncomputable section
open Set
namespace SquaresInCircles

lemma fin_four_other (i : Fin 4) : ∃ j : Fin 4, i ≠ j := by
  by_cases hi : i=0
  · exact ⟨1,by simp [hi]⟩
  · exact ⟨0,hi⟩

/-- The Diamond Lemma in its strict infeasibility form. -/
theorem four_polygon_strict_impossible (S : Fin 4 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P4Strict (alpha (S i) o) (beta (S i) o)) : False := by
  classical
  have h8 (i : Fin 4) := p4Strict_to_p8Strict (alpha_nonneg _ _) (beta_nonneg _ _) (hp i)
  have hcenter (i : Fin 4) : (S i).center ≠ o := by
    obtain ⟨j,hij⟩ := fin_four_other i
    exact center_ne_of_strict_octagons (S i) (S j) o (hd i j hij) (h8 i) (h8 j)
  choose C hsort using (fun i : Fin 4 => sorted_square_chart (S i) o)
  have hsum (i : Fin 4) : (C i).a+(C i).b < 1 := by
    rcases (C i).coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
      dsimp [P4Strict] at hp <;> rw [ha,hb] <;> linarith [hp i]
  have hpos (i : Fin 4) : 0 < (C i).a+(C i).b := by
    have hh := abs_center_sum_pos (S i) o (hcenter i)
    rcases (C i).coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rw [ha,hb] <;> linarith
  obtain ⟨r,hr0,hr1,hrc⟩ := common_four_radius (fun i => (C i).a) (fun i => (C i).b)
    (fun i => (C i).nonneg.1) (fun i => (C i).nonneg.2) hpos hsum
  have harcs : ∀ i : Fin 4, ∃ A : OpenArc o r (rayRegions S o i),
      Real.pi/4 ≤ A.halfWidth ∧
        (¬ openSquare (S i) o → Real.pi/4 < A.halfWidth) := by
    intro i
    by_cases hi : openSquare (S i) o
    · obtain ⟨A,hA⟩ := four_containing_arc (C i) (hsort i) hi (hpos i) (by linarith) hr1
      rw [rayRegions_pos hi]
      exact ⟨A,by rw [hA],fun hn => False.elim (hn hi)⟩
    · obtain ⟨A,hA⟩ := four_exterior_arc (C i) (hsort i) (hsum i) hi hr0 hr1 (hrc i)
      rw [rayRegions_neg hi]
      exact ⟨A,hA.le,fun _ => hA⟩
  choose A hA hstrict using harcs
  have hout : ∃ i : Fin 4, ¬ openSquare (S i) o := by
    by_contra hn
    push Not at hn
    exact hd 0 1 (by decide) o ⟨hn 0,hn 1⟩
  apply uniform_arc_excess (n := 4) (by decide) A
    (rayRegions_disjoint hd (fun i => ⟨(h8 i).1.le,(h8 i).2.le⟩)) hA
  obtain ⟨i,hi⟩ := hout
  exact ⟨i,hstrict i hi⟩

theorem four_squared_lower (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : (2:ℝ) ≤ R^2 := by
  by_contra hn
  exact four_polygon_strict_impossible S o hp.disjoint
    (fun i => p4_of_phi_lt ((hp.phi_le i).trans_lt (lt_of_not_ge hn)))

theorem Four.optimality (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) : Four.radius ≤ R :=
  radius_lower_of_squared hp.1
    (by rw [Four.radius_sq]; exact four_squared_lower S o R hp)

theorem Four.optimality_and_attainment :
    (∀ (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ),
      Packing S o R → Four.radius ≤ R) ∧
    ∃ (S : Fin 4 → UnitSquare) (o : Point), Packing S o Four.radius :=
  ⟨Four.optimality,Four.attainment⟩

end SquaresInCircles
