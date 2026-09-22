import ThreeUnitSquaresInCircle.Concavity

/-! Explicit branch-to-certificate selection. Compiles against Lean 4.34.0 / mathlib v4.34.0.
This file is generated as text. All claims about finite data are Lean `decide`
proof scripts. Generation itself provides no logical evidence. -/
namespace ThreeUnitSquaresInCircle.Cert
open RatData
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 4000
set_option synthInstance.maxHeartbeats 1000000

def table : Fin 53 → Certificate :=
  ![cert000, cert001, cert002, cert003, cert004, cert005, cert006, cert007, cert008, cert009, cert010, cert011, cert012, cert013, cert014, cert015, cert016, cert017, cert018, cert019, cert020, cert021, cert022, cert023, cert024, cert025, cert026, cert027, cert028, cert029, cert030, cert031, cert032, cert033, cert034, cert035, cert036, cert037, cert038, cert039, cert040, cert041, cert042, cert043, cert044, cert045, cert046, cert047, cert048, cert049, cert050, cert051, cert052]

theorem table_checked (i : Fin 53) : arithmeticValid (table i) := by
  fin_cases i <;> decide +kernel

def baseIndex : Fin 48 → Fin 53 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 20, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 47, 48, 49, 50, 52]

def branchK (j : Fin 48) : Fin 3 → Fin 4 := (table (baseIndex j)).k
def branchSource (j : Fin 48) : Fin 3 → Fin 3 := (table (baseIndex j)).source

theorem branch_lookup :
    ∀ k02 k12 : Fin 4, (k02,k12) ∈ Combinatorics.remaining →
    ∀ s0 s1 s2 : Fin 3, (s0,s1,s2) ∈ Combinatorics.sources →
      ∃ j : Fin 48,
        branchK j = ![0,k02,k12] ∧ branchSource j = ![s0,s1,s2] := by
  decide +kernel

noncomputable section

def Covers (j : Fin 48) (x : Point) : Prop :=
  ∃ i : Fin 53, (table i).k = branchK j ∧
    (table i).source = branchSource j ∧
    x ∈ convexHull ℝ (cornerPoint '' {p | p ∈ (table i).corners})

theorem branch_cover (j : Fin 48) (x : Point)
    (hx : AngleDomain.Domain x.1 x.2) : Covers j x := by
  fin_cases j

  ·
    refine ⟨0, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 0).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨1, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 1).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨2, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 2).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨3, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 3).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨4, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 4).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨5, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 5).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨6, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 6).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨7, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 7).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨8, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 8).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨9, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 9).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨10, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 10).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨11, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 11).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  · rcases AngleDomain.cover_G hx with h | h
    ·
      refine ⟨12, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 12).corners .O .V .Z
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    ·
      refine ⟨13, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 13).corners .V .W .Z
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
  ·
    refine ⟨14, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 14).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨15, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 15).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨16, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 16).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨17, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 17).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  · rcases AngleDomain.cover_H hx with h | h
    ·
      refine ⟨18, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 18).corners .O .P .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    ·
      refine ⟨19, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 19).corners .P .V .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
  ·
    refine ⟨20, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 20).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨21, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 21).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨22, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 22).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  · rcases AngleDomain.cover_H hx with h | h
    ·
      refine ⟨23, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 23).corners .O .P .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    ·
      refine ⟨24, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 24).corners .P .V .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
  ·
    refine ⟨25, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 25).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨26, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 26).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨27, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 27).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨28, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 28).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨29, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 29).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨30, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 30).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨31, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 31).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨32, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 32).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨33, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 33).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨34, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 34).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨35, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 35).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨36, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 36).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨37, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 37).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨38, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 38).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨39, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 39).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨40, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 40).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨41, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 41).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨42, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 42).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨43, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 43).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨44, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 44).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  · rcases AngleDomain.cover_H hx with h | h
    ·
      refine ⟨45, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 45).corners .O .P .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    ·
      refine ⟨46, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 46).corners .P .V .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
  ·
    refine ⟨47, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 47).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨48, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 48).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  ·
    refine ⟨49, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 49).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)
  · rcases AngleDomain.cover_J_special hx with h | h | h
    ·
      refine ⟨50, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 50).corners .O .P .Z
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    ·
      refine ⟨51, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 51).corners .P .V .W
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
    ·
      refine ⟨51, by decide +kernel, by decide +kernel, ?_⟩
      exact triangle_subset_hull (table 51).corners .P .W .Z
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
  ·
    refine ⟨52, by decide +kernel, by decide +kernel, ?_⟩
    exact triangle_subset_hull (table 52).corners .O .V .W
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (AngleDomain.in_full hx)

/-- Every surviving source/cardinal pattern has a real-valued valid certificate. -/
theorem select_certificate (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3)
    (hk0 : k 0 = 0)
    (hk : (k 1,k 2) ∈ Combinatorics.remaining)
    (hs : ∀ e, s e = first e ∨ s e = last e)
    (x : Point) (hx : AngleDomain.Domain x.1 x.2) :
    ∃ i : Fin 53, (table i).k = k ∧ (table i).source = s ∧
      targetSq ≤ polynomial (table i) x := by
  have hsv : (s 0,s 1,s 2) ∈ Combinatorics.sources := by
    apply (Combinatorics.source_classification (s 0) (s 1) (s 2)).mp
    simpa [first,last] using And.intro (hs 0) (And.intro (hs 1) (hs 2))
  obtain ⟨j,hjk,hjs⟩ := branch_lookup (k 1) (k 2) hk (s 0) (s 1) (s 2) hsv
  obtain ⟨i,hik,his,hix⟩ := branch_cover j x hx
  refine ⟨i, ?_, ?_, certificate_on_hull (table i) (table_checked i) x hix⟩
  · rw [hik,hjk]
    funext e
    fin_cases e <;> simp [hk0]
  · rw [his,hjs]
    funext e
    fin_cases e <;> simp

end

end ThreeUnitSquaresInCircle.Cert
