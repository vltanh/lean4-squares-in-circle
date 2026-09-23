import SquaresInCircles.Three.Optimality
import SquaresInCircles.Common.Angles

/-!
# Uniqueness of the T

At the optimal radius no square contains the disk centre, and the three
exterior arcs are each exactly 120 degrees. Equality leaves two contact types
for a square; one A-square and two B-squares are the only possibility, and they
are reconstructed into the T for every labelling and chart orientation.
-/
noncomputable section
open Set
namespace SquaresInCircles

/-! ## No square contains the disk centre

At the optimal radius the squares satisfy only the closed 16-gon. A square that
contains the disk centre still satisfies the strict one, which is all that
`three_containing_impossible` asks of it. -/

lemma tangent_strict_of_ne {a b u v K : ℝ}
    (h : phi a b ≤ K) (hc : phi u v=K) (hne : a ≠ u ∨ b ≠ v) :
    2*(u+1/2)*(a-u)+2*(v+1/2)*(b-v) < 0 := by
  have he := tangent_identity a b u v
  have hpos : 0 < (a-u)^2+(b-v)^2 := by
    rcases hne with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr h))
  linarith

lemma p3_strict_of_inside {a b : ℝ} (ha : a < 1/2) (hb : b < 1/2)
    (hφ : phi a b ≤ (425:ℝ)/256) : P3Strict a b := by
  have h₀ := tangent_strict_of_ne (u := 1/2) (v := 5/16) hφ
    (by norm_num [phi]) (Or.inl (ne_of_lt ha))
  have h₁ := tangent_strict_of_ne (u := 5/16) (v := 1/2) hφ
    (by norm_num [phi]) (Or.inr (ne_of_lt hb))
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

/-! ## Reconstruction of the T

The three arc midpoints form an equilateral triple and the two B-contact phases
are antipodal; no numerical angle choices are used. -/

lemma a_contact_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=11/16) (hb : C.b=0) :
    ∃ A : OpenArc o auxThree {p | openSquare S p},
      A.halfWidth=Real.pi/3 ∧ A.center=C.phase := by
  obtain ⟨A,hA,hc⟩ := C.arc auxThree (-(Real.pi/3)) (Real.pi/3)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by
      intro t ht
      have hcos : 1/2 < Real.cos t := by
        have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg t)
          (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) (abs_lt.mpr ht)
        rw [Real.cos_pi_div_three,Real.cos_abs] at hh
        exact hh
      rw [ha,hb]
      dsimp [auxThree]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith [Real.neg_one_le_sin t],by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,by rw [hA]; ring,by rw [hc]; simp [chartAngle]⟩

lemma b_semicircle {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=5/16) :
    ∃ A : OpenArc o (1/16) {p | openSquare S p},
      A.halfWidth=Real.pi/2 ∧ A.center=C.phase := by
  obtain ⟨A,hA,hc⟩ := C.arc (1/16) (-(Real.pi/2)) (Real.pi/2)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by
      intro t ht
      have hc := Real.cos_pos_of_mem_Ioo ht
      rw [ha,hb]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith [Real.neg_one_le_sin t],by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,by rw [hA]; ring,by rw [hc]; simp [chartAngle]⟩

lemma b_contact_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (ha : C.a=1/2) (hb : C.b=5/16) :
    ∃ A : OpenArc o auxThree {p | openSquare S p}, A.halfWidth=Real.pi/3 ∧
      A.center=chartAngle C.phase C.reversed (Real.pi/6) := by
  obtain ⟨A,hA,hc⟩ := C.arc auxThree (-Real.pi/6) (Real.pi/2)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) (by
      intro t ht
      have hcos := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
      have hsin := Real.strictMonoOn_sin
        (show -Real.pi/6 ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [Real.pi_pos])
        (show t ∈ Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [ht.1,ht.2,Real.pi_pos]) ht.1
      rw [neg_div,Real.sin_neg,Real.sin_pi_div_six] at hsin
      rw [ha,hb]
      dsimp [auxThree]
      exact ⟨abs_lt.mpr ⟨by linarith,by linarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by linarith,by linarith [Real.sin_le_one t]⟩⟩)
  exact ⟨A,by rw [hA]; ring,by convert hc using 2; ring⟩

lemma equilateral_arc_centers {o : Point} {r : ℝ} {U V W : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (G : OpenArc o r W)
    (ha : A.halfWidth=Real.pi/3) (hb : B.halfWidth=Real.pi/3) (hg : G.halfWidth=Real.pi/3)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    dist A.center B.center=2*Real.pi/3 ∧
    dist A.center G.center=2*Real.pi/3 ∧
    dist B.center G.center=2*Real.pi/3 := by
  have h₁ := G.third_distance_bounds A B hUW.symm hVW.symm hUV
  have h₂ := B.third_distance_bounds A G hUV.symm hVW hUW
  have h₃ := A.third_distance_bounds B G hUV hUW hVW
  exact ⟨by linarith [h₁.1,h₁.2],by linarith [h₂.1,h₂.2],by linarith [h₃.1,h₃.2]⟩

lemma two_a_contacts_impossible {S T U : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o)
    (hc : C.a=11/16 ∧ C.b=0) (hd : D.a=11/16 ∧ D.b=0)
    (G : OpenArc o auxThree {p | openSquare U p}) (hg : Real.pi/3 ≤ G.halfWidth)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (hSU : Disjoint {p | openSquare S p} {p | openSquare U p})
    (hTU : Disjoint {p | openSquare T p} {p | openSquare U p}) : False := by
  obtain ⟨A,ha,hac⟩ := a_contact_arc C hc.1 hc.2
  obtain ⟨B,hb,hbc⟩ := a_contact_arc D hd.1 hd.2
  have hdist := G.third_distance_bounds A B hSU.symm hTU.symm hST
  rw [ha,hb,hac,hbc] at hdist
  obtain ⟨p,hpS,hpT⟩ := near_axis_square_overlap C D
    ⟨by linarith [hc.1],by linarith [hc.1]⟩ (by linarith [hc.2])
    ⟨by linarith [hd.1],by linarith [hd.1]⟩ (by linarith [hd.2])
    (by linarith [hdist.1]) (by linarith [hdist.2])
  exact Set.disjoint_left.mp hST hpS hpT

lemma three_b_contacts_impossible {S T U : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) (E : SquareChart U o)
    (hc : C.a=1/2 ∧ C.b=5/16) (hd : D.a=1/2 ∧ D.b=5/16)
    (he : E.a=1/2 ∧ E.b=5/16)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (hSU : Disjoint {p | openSquare S p} {p | openSquare U p})
    (hTU : Disjoint {p | openSquare T p} {p | openSquare U p}) : False := by
  obtain ⟨A,ha,_⟩ := b_semicircle C hc.1 hc.2
  obtain ⟨B,hb,_⟩ := b_semicircle D hd.1 hd.2
  obtain ⟨G,hg,_⟩ := b_semicircle E he.1 he.2
  have h := triple_arc_budget A B G hST hSU hTU
  rw [ha,hb,hg] at h
  linarith [Real.pi_pos]

/-- Trigonometric reconstruction of the radial phase of the remaining A-square. -/
lemma apex_phase {φ ψ χ : Direction} (r s : Bool)
    (hanti : ψ=φ+(Real.pi:Direction))
    (h01 : (chartAngle ψ s (Real.pi/6)-chartAngle φ r (Real.pi/6)).cos= -(1/2))
    (h02 : (χ-chartAngle φ r (Real.pi/6)).cos= -(1/2))
    (h12 : (χ-chartAngle ψ s (Real.pi/6)).cos= -(1/2)) :
    s= !r ∧ (χ-φ).cos=0 ∧ (χ-φ).sin=(if r then 1 else -1) := by
  let δ := χ-φ
  let p : Direction := ((Real.pi/6:ℝ):Direction)
  have hcp : p.cos=Real.sqrt 3/2 := by simp [p,Real.cos_pi_div_six]
  have hsp : p.sin=(1/2:ℝ) := by simp [p,Real.sin_pi_div_six]
  cases r <;> cases s
  · have he : chartAngle ψ false (Real.pi/6)-chartAngle φ false (Real.pi/6)=(Real.pi:Direction) := by
      rw [hanti]; simp only [chartAngle,Bool.false_eq_true,ite_false]; abel
    rw [he,Real.Angle.cos_coe,Real.cos_pi] at h01
    norm_num at h01
  · have he₀ : χ-chartAngle φ false (Real.pi/6)=δ-p := by
      simp only [δ,p,chartAngle,Bool.false_eq_true,ite_false]; abel
    have he₁ : χ-chartAngle ψ true (Real.pi/6)=δ-(Real.pi:Direction)+p := by
      rw [hanti]; simp only [δ,p,chartAngle,ite_true,Real.Angle.coe_neg]; abel
    rw [he₀] at h02
    rw [he₁] at h12
    simp only [sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_neg,
      Real.Angle.sin_neg,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi,Real.sin_pi,
      hcp,hsp] at h02 h12
    have hs : δ.sin= -1 := by linarith
    have hc : δ.cos=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq δ]
    exact ⟨rfl,hc,hs⟩
  · have he₀ : χ-chartAngle φ true (Real.pi/6)=δ+p := by
      simp only [δ,p,chartAngle,ite_true,Real.Angle.coe_neg]; abel
    have he₁ : χ-chartAngle ψ false (Real.pi/6)=δ-(Real.pi:Direction)-p := by
      rw [hanti]; simp only [δ,p,chartAngle,Bool.false_eq_true,ite_false]; abel
    rw [he₀] at h02
    rw [he₁] at h12
    simp only [sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,Real.Angle.cos_neg,
      Real.Angle.sin_neg,Real.Angle.cos_coe,Real.Angle.sin_coe,Real.cos_pi,Real.sin_pi,
      hcp,hsp] at h02 h12
    have hs : δ.sin=1 := by linarith
    have hc : δ.cos=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq δ]
    exact ⟨rfl,hc,hs⟩
  · have he : chartAngle ψ true (Real.pi/6)-chartAngle φ true (Real.pi/6)=(Real.pi:Direction) := by
      rw [hanti]; simp only [chartAngle,ite_true]; abel
    rw [he,Real.Angle.cos_coe,Real.cos_pi] at h01
    norm_num at h01

/-- Two B-contacts and one A-contact reconstruct the T in a single frame. -/
lemma t_contact_reconstruction {S T U : UnitSquare} {o : Point}
    (C : SquareChart S o) (D : SquareChart T o) (E : SquareChart U o)
    (hc : C.a=1/2 ∧ C.b=5/16) (hd : D.a=1/2 ∧ D.b=5/16)
    (he : E.a=11/16 ∧ E.b=0)
    (hST : Disjoint {p | openSquare S p} {p | openSquare T p})
    (hSU : Disjoint {p | openSquare S p} {p | openSquare U p})
    (hTU : Disjoint {p | openSquare T p} {p | openSquare U p}) :
    ∃ φ : Direction,
      ((Represents S o φ (Three.centers 0) ∧ Represents T o φ (Three.centers 1)) ∨
       (Represents S o φ (Three.centers 1) ∧ Represents T o φ (Three.centers 0))) ∧
      Represents U o φ (Three.centers 2) := by
  obtain ⟨A,ha,hac⟩ := b_contact_arc C hc.1 hc.2
  obtain ⟨B,hb,hbc⟩ := b_contact_arc D hd.1 hd.2
  obtain ⟨G,hg,hgc⟩ := a_contact_arc E he.1 he.2
  have hdist := equilateral_arc_centers A B G ha hb hg hST hSU hTU
  rw [hac,hbc,hgc] at hdist
  obtain ⟨A',ha',hac'⟩ := b_semicircle C hc.1 hc.2
  obtain ⟨B',hb',hbc'⟩ := b_semicircle D hd.1 hd.2
  have hanti : D.phase=C.phase+(Real.pi:Direction) := by
    apply antipodal_of_distance
    have hh := A'.centers_separated B' hST
    rw [ha',hb',hac',hbc'] at hh
    have hu := direction_diameter C.phase D.phase
    linarith
  have h01 := cos_sub_distance (chartAngle C.phase C.reversed (Real.pi/6))
    (chartAngle D.phase D.reversed (Real.pi/6))
  have h02 := cos_sub_distance (chartAngle C.phase C.reversed (Real.pi/6)) E.phase
  have h12 := cos_sub_distance (chartAngle D.phase D.reversed (Real.pi/6)) E.phase
  rw [hdist.1,cos_two_pi_thirds] at h01
  rw [hdist.2.1,cos_two_pi_thirds] at h02
  rw [hdist.2.2,cos_two_pi_thirds] at h12
  obtain ⟨hrev,hEcos,hEsin⟩ := apex_phase C.reversed D.reversed hanti h01 h02 h12
  have hC := chart_represents C
  have hD := chart_represents D
  have hE := chart_represents E
  cases hr : C.reversed
  · have hrD : D.reversed=true := by simpa only [hr,Bool.not_false] using hrev
    let φ := C.phase+(Real.pi:Direction)
    have hCc : (C.phase-φ).cos= -1 := by
      have hh : C.phase-φ= -(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh]; simp
    have hCs : (C.phase-φ).sin=0 := by
      have hh : C.phase-φ= -(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh]; simp
    have hDφ : D.phase=φ := hanti
    have hEc : (E.phase-φ).cos=0 := by
      have hh : E.phase-φ=(E.phase-C.phase)-(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh,Real.Angle.cos_sub_pi,hEcos]; ring
    have hEs : (E.phase-φ).sin=1 := by
      have hh : E.phase-φ=(E.phase-C.phase)-(Real.pi:Direction) := by dsimp [φ]; abel
      rw [hh,Real.Angle.sin_sub_pi]
      simpa only [hr,Bool.false_eq_true,ite_false,neg_neg] using congrArg Neg.neg hEsin
    have rC := represents_cardinal (ψ := φ) hC 2 (by simpa [quarterShift] using hCc)
      (by simpa [quarterShift] using hCs)
    have rD := represents_cardinal (ψ := φ) hD 0 (by simp [hDφ,quarterShift]) (by simp [hDφ,quarterShift])
    have rE := represents_cardinal (ψ := φ) hE 1 (by simpa [quarterShift] using hEc)
      (by simpa [quarterShift] using hEs)
    refine ⟨φ,Or.inl ⟨?_,?_⟩,?_⟩
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,hr,hc.1,hc.2] using rC
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,hrD,hd.1,hd.2] using rD
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,he.1,he.2] using rE
  · have hrD : D.reversed=false := by simpa only [hr,Bool.not_true] using hrev
    let φ := C.phase
    have rC : Represents S o φ (Three.centers 1) := by
      simpa [neg_div,φ,Three.centers,SquareChart.signedB,hr,hc.1,hc.2] using hC
    have rD := represents_cardinal (ψ := φ) hD 2
      (by simp [φ,hanti,quarterShift]) (by simp [φ,hanti,quarterShift])
    have rE := represents_cardinal (ψ := φ) hE 1
      (by simpa [φ,quarterShift] using hEcos)
      (by simpa [φ,quarterShift,hr] using hEsin)
    refine ⟨φ,Or.inr ⟨rC,?_⟩,?_⟩
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,hrD,hd.1,hd.2] using rD
    · simpa [neg_div,turnPoint,Three.centers,SquareChart.signedB,he.1,he.2] using rE

/-! ## Assembly -/

lemma three_no_containing (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hφ : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ (425:ℝ)/256) :
    ∀ i, ¬ openSquare (S i) o := fun i hi =>
  three_containing_impossible S o hd i hi (p3_strict_of_inside hi.1 hi.2 (hφ i))
    fun j => p3_of_phi_le (hφ j)

lemma assemble_three {S : Fin 3 → UnitSquare} {o : Point} (hd : InteriorDisjoint S)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h : ∃ φ : Direction,
      ((Represents (S i) o φ (Three.centers 0) ∧ Represents (S j) o φ (Three.centers 1)) ∨
       (Represents (S i) o φ (Three.centers 1) ∧ Represents (S j) o φ (Three.centers 0))) ∧
      Represents (S k) o φ (Three.centers 2)) : HasNormalForm S o Three.centers := by
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
theorem Three.uniqueness (S : Fin 3 → UnitSquare) (o : Point)
    (hp : Packing S o Three.radius) : HasNormalForm S o Three.centers := by
  classical
  have hφ (i : Fin 3) : phi (alpha (S i) o) (beta (S i) o) ≤ (425:ℝ)/256 := by
    have h := hp.phi_le i
    rwa [Three.radius_sq] at h
  have hout := three_no_containing S o hp.disjoint hφ
  have hpair := hp.disjoint.pairwise
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hpC (i : Fin 3) : P3 (C i).a (C i).b :=
    (C i).transfer P3 p3_swap (p3_of_phi_le (hφ i))
  have haC (i : Fin 3) : 1/2 ≤ (C i).a := (C i).exterior (hsort i) (hout i)
  choose A hlen using (fun i => (three_cap_arc_formula (C i) (haC i) (hpC i)).imp
    fun _ h => h.1)
  have hlo (i : Fin 3) : Real.pi/3 ≤ (A i).halfWidth := by
    have hh := (three_cap_data (haC i) (C i).nonneg.2 (hpC i)).2.2.2.2.2
    linarith [hlen i]
  have hbudget := open_arc_budget A hpair
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
    obtain ⟨k,hik,hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
      fin_cases i <;> fin_cases j
      all_goals first | exact (hij rfl).elim | decide
    exact two_a_contacts_impossible (C i) (C j) hi hj (A k) (hlo k)
      (hpair hij) (hpair hik) (hpair hjk)
  have hex : ∃ k : Fin 3, (C k).a=11/16 ∧ (C k).b=0 := by
    by_contra hn
    push Not at hn
    have hb (i : Fin 3) : (C i).a=1/2 ∧ (C i).b=5/16 :=
      (htype i).resolve_left (by intro h; exact hn i h.1 h.2)
    exact three_b_contacts_impossible (C 0) (C 1) (C 2) (hb 0) (hb 1) (hb 2)
      (hpair (by decide)) (hpair (by decide)) (hpair (by decide))
  obtain ⟨k,hk⟩ := hex
  have hb (i : Fin 3) (hik : i ≠ k) : (C i).a=1/2 ∧ (C i).b=5/16 :=
    (htype i).resolve_left (fun hi => hnotTwo i k hik hi hk)
  obtain ⟨i,j,hij,hik,hjk⟩ : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    fin_cases k <;> decide
  exact assemble_three hp.disjoint i j k hij hik hjk
    (t_contact_reconstruction (C i) (C j) (C k) (hb i hik) (hb j hjk) hk
      (hpair hij) (hpair hik) (hpair hjk))

end SquaresInCircles
