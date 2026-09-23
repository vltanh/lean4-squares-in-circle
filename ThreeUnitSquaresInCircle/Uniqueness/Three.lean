import ThreeUnitSquaresInCircle.Uniqueness.ThreeReconstruction
import ThreeUnitSquaresInCircle.ThreeArc

/-! Uniqueness of the T packing at radius 5*sqrt(17)/16.  The endpoint uses
the original Packing predicate and the arc framework, not the legacy tables. -/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Uniqueness
open Unified

lemma three_no_containing (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ (425:ℝ)/256) :
    ∀ i, ¬ openSquare (S i) o := by
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p} :=
    Set.disjoint_left.mpr (fun p hi hj => hd i j hij p ⟨hi,hj⟩)
  have hclosed (i : Fin 3) := p3_of_phi_le (hφ i)
  intro i hi
  have hstrict : P3Strict (alpha (S i) o) (beta (S i) o) :=
    p3_strict_of_inside hi.1 hi.2 (hφ i)
  fin_cases i
  · exact three_containing_closed_impossible (S 0) (S 1) (S 2) o
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
      hstrict (hclosed 1) (hclosed 2) hi
  · exact three_containing_closed_impossible (S 1) (S 0) (S 2) o
      (hpair 1 0 (by decide)) (hpair 1 2 (by decide)) (hpair 0 2 (by decide))
      hstrict (hclosed 0) (hclosed 2) hi
  · exact three_containing_closed_impossible (S 2) (S 0) (S 1) o
      (hpair 2 0 (by decide)) (hpair 2 1 (by decide)) (hpair 0 1 (by decide))
      hstrict (hclosed 0) (hclosed 1) hi

lemma assemble_three {S : Fin 3 → UnitSquare} {o : Point} (hd : InteriorDisjoint S)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : ∃ φ : Direction,
      ((Represents (S i) o φ (threeCenters 0) ∧ Represents (S j) o φ (threeCenters 1)) ∨
       (Represents (S i) o φ (threeCenters 1) ∧ Represents (S j) o φ (threeCenters 0))) ∧
      Represents (S k) o φ (threeCenters 2)) : HasNormalForm S o threeCenters := by
  have hcover : ∀ l : Fin 3, l=i ∨ l=j ∨ l=k := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim | decide
  obtain ⟨φ,hij',hk⟩ := h
  apply normal_form_of_slots (φ := φ) hd
  intro l
  rcases hcover l with rfl | rfl | rfl
  · rcases hij' with h | h
    · exact ⟨0,h.1⟩
    · exact ⟨1,h.1⟩
  · rcases hij' with h | h
    · exact ⟨1,h.2⟩
    · exact ⟨0,h.2⟩
  · exact ⟨2,hk⟩

/-- Every optimal three-square packing is one rigid image of the T model. -/
theorem three_uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o optimalRadius) : HasNormalForm S o threeCenters := by
  classical
  have hpN : PackingN S o optimalRadius := hp
  have hφ (i : Fin 3) : phi (alpha (S i) o) (beta (S i) o) ≤ (425:ℝ)/256 := by
    have h := hpN.phi_le i
    simpa only [optimalRadius_sq,targetSq] using h
  have hout := three_no_containing S o hpN.disjoint hφ
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p} :=
    Set.disjoint_left.mpr (fun p hi hj => hpN.disjoint i j hij p ⟨hi,hj⟩)
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hpC (i : Fin 3) : P3 (C i).a (C i).b :=
    p3_chart (C i) (p3_of_phi_le (hφ i))
  have haC (i : Fin 3) : 1/2 ≤ (C i).a := (C i).exterior (hsort i) (hout i)
  choose A hlen using (fun i => three_cap_arc_formula_closed (C i) (haC i) (hpC i))
  have hlo (i : Fin 3) : Real.pi/3 ≤ (A i).halfWidth := by
    have hh := (three_cap_data_closed (haC i) (C i).nonneg.2 (hpC i)).2.2.2.2.2
    linarith [hlen i]
  have hbudget := open_arc_budget A (fun i j hij => hpair i j hij)
  rw [Fin.sum_univ_three] at hbudget
  have hup (i : Fin 3) : threeCapLength (C i).a (C i).b ≤ 2*Real.pi/3 := by
    have key : i=0 ∨ i=1 ∨ i=2 := by revert i; decide
    rcases key with rfl | rfl | rfl <;> linarith [hlo 0,hlo 1,hlo 2,hlen 0,hlen 1,hlen 2]
  have htype (i : Fin 3) : ((C i).a=11/16 ∧ (C i).b=0) ∨
      ((C i).a=1/2 ∧ (C i).b=5/16) :=
    three_cap_contact_types (haC i) (C i).nonneg.2 (hpC i) (hup i)
  have hnotTwo (i j : Fin 3) (hij : i ≠ j)
      (hi : (C i).a=11/16 ∧ (C i).b=0)
      (hj : (C j).a=11/16 ∧ (C j).b=0) : False := by
    have hthird : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | decide
    obtain ⟨k,hik,hjk⟩ := hthird
    exact two_a_contacts_impossible (C i) (C j) hi hj (A k) (hlo k)
      (hpair i j hij) (hpair i k hik) (hpair j k hjk)
  have hex : ∃ k : Fin 3, (C k).a=11/16 ∧ (C k).b=0 := by
    by_contra hn
    push Not at hn
    have hb (i : Fin 3) : (C i).a=1/2 ∧ (C i).b=5/16 :=
      (htype i).resolve_left (by intro h; exact hn i h.1 h.2)
    exact three_b_contacts_impossible (C 0) (C 1) (C 2) (hb 0) (hb 1) (hb 2)
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
  obtain ⟨k,hk⟩ := hex
  have hb (i : Fin 3) (hik : i ≠ k) : (C i).a=1/2 ∧ (C i).b=5/16 :=
    (htype i).resolve_left (fun hi => hnotTwo i k hik hi hk)
  fin_cases k
  · apply assemble_three hpN.disjoint 1 2 0 (by decide) (by decide) (by decide)
    exact t_contact_reconstruction (C 1) (C 2) (C 0)
      (hb 1 (by decide)) (hb 2 (by decide)) hk
      (hpair 1 2 (by decide)) (hpair 1 0 (by decide)) (hpair 2 0 (by decide))
  · apply assemble_three hpN.disjoint 0 2 1 (by decide) (by decide) (by decide)
    exact t_contact_reconstruction (C 0) (C 2) (C 1)
      (hb 0 (by decide)) (hb 2 (by decide)) hk
      (hpair 0 2 (by decide)) (hpair 0 1 (by decide)) (hpair 2 1 (by decide))
  · apply assemble_three hpN.disjoint 0 1 2 (by decide) (by decide) (by decide)
    exact t_contact_reconstruction (C 0) (C 1) (C 2)
      (hb 0 (by decide)) (hb 1 (by decide)) hk
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))

end ThreeUnitSquaresInCircle.Uniqueness
