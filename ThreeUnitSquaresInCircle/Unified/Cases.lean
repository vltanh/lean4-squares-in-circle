import ThreeUnitSquaresInCircle.Unified.ArcGeometry

/-!
# Assembly of the three arc proofs

The theorem names end in `_draft`: they depend on the six explicitly admitted
geometric obligations in ArcGeometry.lean. The finite-family measure argument
and tangent reductions are separate from those obligations.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified
open Set Filter
open scoped Topology BigOperators

private lemma eventually_all_four {f : ℝ → Fin 4 → Prop}
    (h : ∀ i, ∀ᶠ r in 𝓝[<] r4, f r i) :
    ∀ᶠ r in 𝓝[<] r4, ∀ i, f r i := by
  filter_upwards [h 0,h 1,h 2,h 3] with r h0 h1 h2 h3
  intro i
  fin_cases i <;> assumption

theorem no_three_strict_polygon_draft (S : Fin 3 → UnitSquare) (o : Point)
    (hd : Nonoverlapping S) (hP : ∀ i, CenterBody P3Strict (S i) o) : False := by
  classical
  by_cases hin : ∃ i, openSquare (S i) o
  · obtain ⟨i,hi⟩ := hin
    obtain ⟨j,k,U,V,hjk,hU,hV,⟨hcaps⟩⟩ := containing_three_caps S o hd hP i hi
    obtain ⟨hp,hq⟩ := hcaps.overlap
    exact hd j k hjk hcaps.point ⟨(hU.2 _).mp hp,(hV.2 _).mp hq⟩
  · have hout : ∀ i, ¬ openSquare (S i) o := by simpa using hin
    have hm := occupied_budget hd o r3
    exact no_uniform_strict_budget (by norm_num : 0 < 3) _ hm
      (fun i => exterior_three_mass (S i) o (hP i) (hout i))

theorem no_four_strict_diamond_draft (S : Fin 4 → UnitSquare) (o : Point)
    (hd : Nonoverlapping S) (hP : ∀ i, CenterBody P4Strict (S i) o) : False := by
  classical
  have h8s : ∀ i, CenterBody OctagonStrict (S i) o := fun i =>
    P4Strict.octagonStrict (alpha_nonneg _ _) (beta_nonneg _ _) (hP i)
  have h8 : ∀ i, CenterBody Octagon (S i) o := fun i => ⟨(h8s i).1.le,(h8s i).2.le⟩
  have hne := centers_ne_of_strict_octagon S o hd h8s
  have hm : ∀ i, ∀ᶠ r in 𝓝[<] r4,
      Real.pi/2 < angularMass (safePiece S o i) o r := by
    intro i
    by_cases hi : openSquare (S i) o
    · simpa only [safePiece, if_pos hi] using
        extension_four_eventually (S i) o hi (hne i)
    · simpa only [safePiece, if_neg hi, occupied] using
        exterior_four_eventually (S i) o (hP i) hi
  obtain ⟨r,hr⟩ := (eventually_all_four hm).exists
  apply no_uniform_strict_budget (by norm_num : 0 < 4)
    (fun i => angularMass (safePiece S o i) o r) (safePieces_budget S o hd h8 r)
  intro i
  simpa using hr i

theorem no_five_strict_dodecagon_draft (S : Fin 5 → UnitSquare) (o : Point)
    (hd : Nonoverlapping S) (hP : ∀ i, CenterBody P5Strict (S i) o) : False := by
  classical
  have h8s : ∀ i, CenterBody OctagonStrict (S i) o := fun i => (hP i).1
  have h8 : ∀ i, CenterBody Octagon (S i) o := fun i => ⟨(h8s i).1.le,(h8s i).2.le⟩
  have hne := centers_ne_of_strict_octagon S o hd h8s
  have hm : ∀ i, 2*Real.pi/5 < angularMass (safePiece S o i) o r5 := by
    intro i
    by_cases hi : openSquare (S i) o
    · simpa only [safePiece, if_pos hi] using
        extension_five_mass (S i) o hi (hne i)
    · simpa only [safePiece, if_neg hi, occupied] using
        exterior_five_mass (S i) o (hP i).le hi
  exact no_uniform_strict_budget (by norm_num : 0 < 5) _
    (safePieces_budget S o hd h8 r5) hm

theorem three_radius_lower_arc_draft (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : optimalRadius ≤ R := by
  apply radius_lower_of_squared hp.1
  by_contra hh
  have hr : R^2 < 425/256 := by
    simpa only [targetSq] using lt_of_not_ge hh
  exact no_three_strict_polygon_draft S o hp.2.2 fun i =>
    phi_P3Strict ((phi_le_radius_sq (hp.2.1 i)).trans_lt hr)

theorem four_radius_lower_arc_draft (S : Fin 4 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : Real.sqrt 2 ≤ R := by
  apply sqrt_le_of_sq_le (by norm_num) hp.1
  by_contra hh
  have hr : R^2 < 2 := lt_of_not_ge hh
  exact no_four_strict_diamond_draft S o hp.2.2 fun i =>
    phi_P4Strict ((phi_le_radius_sq (hp.2.1 i)).trans_lt hr)

theorem five_radius_lower_arc_draft (S : Fin 5 → UnitSquare) (o : Point) (R : ℝ)
    (hp : PackingN S o R) : Real.sqrt (5/2) ≤ R := by
  apply sqrt_le_of_sq_le (by norm_num) hp.1
  by_contra hh
  have hr : R^2 < 5/2 := lt_of_not_ge hh
  exact no_five_strict_dodecagon_draft S o hp.2.2 fun i =>
    phi_P5Strict ((phi_le_radius_sq (hp.2.1 i)).trans_lt hr)

end ThreeUnitSquaresInCircle.Unified
