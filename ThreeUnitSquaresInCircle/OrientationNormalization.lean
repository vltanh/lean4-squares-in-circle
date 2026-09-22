import ThreeUnitSquaresInCircle.PlaneTools

/-! Three-angle cyclic normalization, including ties and boundary angles. -/
noncomputable section
namespace ThreeUnitSquaresInCircle.Cert

lemma sort_three (t : Fin 3 → ℝ) :
    ∃ σ : Fin 3 → Fin 3, Function.Injective σ ∧
      t (σ 0) ≤ t (σ 1) ∧ t (σ 1) ≤ t (σ 2) := by
  rcases le_total (t 0) (t 1) with h01 | h10
  · rcases le_total (t 1) (t 2) with h12 | h21
    · exact ⟨![0,1,2], by decide, h01, h12⟩
    · rcases le_total (t 0) (t 2) with h02 | h20
      · exact ⟨![0,2,1], by decide, h02, h21⟩
      · exact ⟨![2,0,1], by decide, h20, h01⟩
  · rcases le_total (t 0) (t 2) with h02 | h20
    · exact ⟨![1,0,2], by decide, h10, h02⟩
    · rcases le_total (t 1) (t 2) with h12 | h21
      · exact ⟨![1,2,0], by decide, h12, h20⟩
      · exact ⟨![2,1,0], by decide, h21, h10⟩

lemma packing_cut {c : Fin 3 → Point} {t : Fin 3 → ℝ} {R : ℝ}
    (hp : Packing (afamily c t) (0,0) R)
    (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ)
    (lift : Fin 3 → Bool) (r : ℝ) :
    Packing (afamily (fun i => rotation (-r) (c (σ i)))
      (fun i => (-r+t (σ i)) + if lift i then quarter else 0)) (0,0) R := by
  exact packing_lift_quarters
    (packing_rotate_angles (packing_reindex hp σ hσ) (-r)) lift

/-- Cut immediately after a largest cyclic gap. Both remaining gaps are no larger
than the omitted one. No division or strict ordering is used. -/
lemma largest_gap_cut {c : Fin 3 → Point} {u v w R : ℝ}
    (hp : Packing (afamily c ![u,v,w]) (0,0) R)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvw : v ≤ w) (hw : w ≤ quarter) :
    ∃ (c' : Fin 3 → Point) (a b : ℝ),
      0 ≤ a ∧ a ≤ b ∧ a ≤ quarter-b ∧ b-a ≤ quarter-b ∧
      Packing (afamily c' ![0,a,b]) (0,0) R := by
  by_cases hout : v-u ≤ quarter-(w-u) ∧ w-v ≤ quarter-(w-u)
  · let σ : Fin 3 → Fin 3 := ![0,1,2]
    have h := packing_cut hp σ (by decide) (fun _ => false) u
    have ht : (fun i => (-u+(![u,v,w] : Fin 3 → ℝ) (σ i)) +
        if false then quarter else 0) = ![0,v-u,w-u] := by
      funext i; fin_cases i <;> norm_num [σ] <;> ring
    rw [ht] at h
    exact ⟨_, v-u, w-u, by linarith, by linarith, hout.1, by linarith [hout.2], h⟩
  · by_cases hmax : w-v ≤ v-u
    · have hg : quarter-(w-u) ≤ v-u := by
        by_contra hn
        apply hout
        constructor <;> linarith
      let σ : Fin 3 → Fin 3 := ![1,2,0]
      let lift : Fin 3 → Bool := ![false,false,true]
      have h := packing_cut hp σ (by decide) lift v
      have ht : (fun i => (-v+(![u,v,w] : Fin 3 → ℝ) (σ i)) +
          if lift i then quarter else 0) = ![0,w-v,u+quarter-v] := by
        funext i; fin_cases i <;> norm_num [σ,lift] <;> ring
      rw [ht] at h
      refine ⟨_, w-v, u+quarter-v, ?_, ?_, ?_, ?_, h⟩ <;> linarith
    · have hg : quarter-(w-u) ≤ w-v := by
        by_contra hn
        apply hout
        constructor <;> linarith
      let σ : Fin 3 → Fin 3 := ![2,0,1]
      let lift : Fin 3 → Bool := ![false,true,true]
      have h := packing_cut hp σ (by decide) lift w
      have ht : (fun i => (-w+(![u,v,w] : Fin 3 → ℝ) (σ i)) +
          if lift i then quarter else 0) = ![0,u+quarter-w,v+quarter-w] := by
        funext i; fin_cases i <;> norm_num [σ,lift] <;> ring
      rw [ht] at h
      refine ⟨_, u+quarter-w, v+quarter-w, ?_, ?_, ?_, ?_, h⟩ <;> linarith

lemma reflect_gap_order {c : Fin 3 → Point} {a b R : ℝ}
    (hp : Packing (afamily c ![0,a,b]) (0,0) R) :
    ∃ c' : Fin 3 → Point, Packing (afamily c' ![0,b-a,b]) (0,0) R := by
  let σ : Fin 3 → Fin 3 := ![2,1,0]
  have h := packing_reflect_angles
    (packing_rotate_angles (packing_reindex hp σ (by decide)) (-b))
  have ht : (fun i => -(-b + (![0,a,b] : Fin 3 → ℝ) (σ i))) = ![0,b-a,b] := by
    funext i; fin_cases i <;> norm_num [σ] <;> ring
  rw [ht] at h
  exact ⟨_,h⟩

lemma normalize_angle_units {a b : ℝ} (ha : 0 ≤ a) (hab : 2*a ≤ b)
    (hgap : b-a ≤ quarter-b) :
    ∃ x : Point, AngleDomain.Domain x.1 x.2 ∧ theta x = ![0,a,b] := by
  refine ⟨(a/Real.pi,b/Real.pi), ?_, ?_⟩
  · refine ⟨div_nonneg ha Real.pi_pos.le, ?_, ?_⟩
    · have h := (div_le_div_iff_of_pos_right Real.pi_pos).2 hab
      convert h using 1; ring
    · have h := (div_le_div_iff_of_pos_right Real.pi_pos).2
        (show 2*b-a ≤ Real.pi/2 by
          have hgap' : b - a ≤ Real.pi/2 - b := hgap
          linarith)
      convert h using 1
      · ring
      · field_simp
  · funext i
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    fin_cases i <;> simp [theta] <;> field_simp

/-- Every arbitrary packing has a representative in the full angle triangle. -/
theorem normalize_orientations (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ)
    (hp : Packing S o R) :
    ∃ (c : Fin 3 → Point) (x : Point),
      AngleDomain.Domain x.1 x.2 ∧ Packing (angularSquares c x) (0,0) R := by
  obtain ⟨c,t,ht,hpt⟩ := packing_angle_representatives hp
  obtain ⟨σ,hσ,h01,h12⟩ := sort_three t
  have hs := packing_reindex hpt σ hσ
  have he : (fun i => t (σ i)) = ![t (σ 0),t (σ 1),t (σ 2)] := by
    funext i; fin_cases i <;> rfl
  change Packing (afamily (fun i => c (σ i)) (fun i => t (σ i))) (0,0) R at hs
  rw [he] at hs
  obtain ⟨c',a,b,ha,hab,hga,hgb,hp'⟩ :=
    largest_gap_cut hs (ht (σ 0)).1 h01 h12 (ht (σ 2)).2
  by_cases hsmall : 2*a ≤ b
  · obtain ⟨x,hx,heθ⟩ := normalize_angle_units ha hsmall hgb
    refine ⟨c',x,hx,?_⟩
    change Packing (afamily c' (theta x)) (0,0) R
    rw [heθ]
    exact hp'
  · obtain ⟨c'',hp''⟩ := reflect_gap_order hp'
    obtain ⟨x,hx,heθ⟩ := normalize_angle_units
      (show 0 ≤ b-a by linarith) (show 2*(b-a) ≤ b by linarith)
      (show b-(b-a) ≤ quarter-b by linarith)
    refine ⟨c'',x,hx,?_⟩
    change Packing (afamily c'' (theta x)) (0,0) R
    rw [heθ]
    exact hp''

end ThreeUnitSquaresInCircle.Cert
