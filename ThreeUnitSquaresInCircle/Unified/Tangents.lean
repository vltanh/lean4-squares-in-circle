import ThreeUnitSquaresInCircle.Unified.Basic

/-!
# Contact tangents for three, four and five squares

The strict forms are what an optimality proof by contradiction needs.
The non-strict forms remain useful for subsequent rigidity statements.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

/-- Exact tangent-plus-remainder identity, valid at every proposed contact. -/
theorem tangent_identity (a b u v : ℝ) :
    phi a b - phi u v =
      2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) + (a-u)^2 + (b-v)^2 := by
  unfold phi; ring

theorem tangent_le {a b u v R2 : ℝ} (h : phi a b ≤ R2) (hc : phi u v = R2) :
    2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) ≤ 0 := by
  have hid := tangent_identity a b u v
  nlinarith [sq_nonneg (a-u), sq_nonneg (b-v)]

theorem tangent_lt {a b u v R2 : ℝ} (h : phi a b < R2) (hc : phi u v = R2) :
    2*(u+1/2)*(a-u) + 2*(v+1/2)*(b-v) < 0 := by
  have hid := tangent_identity a b u v
  nlinarith [sq_nonneg (a-u), sq_nonneg (b-v)]

def P3 (a b : ℝ) : Prop :=
  16*a+13*b ≤ 193/16 ∧ 13*a+16*b ≤ 193/16 ∧
  19*a+8*b ≤ 209/16 ∧ 8*a+19*b ≤ 209/16

def P3Strict (a b : ℝ) : Prop :=
  16*a+13*b < 193/16 ∧ 13*a+16*b < 193/16 ∧
  19*a+8*b < 209/16 ∧ 8*a+19*b < 209/16

def P4 (a b : ℝ) : Prop := a+b ≤ 1
def P4Strict (a b : ℝ) : Prop := a+b < 1

def P8 (a b : ℝ) : Prop := 3*a+b ≤ 3 ∧ a+3*b ≤ 3
def P8Strict (a b : ℝ) : Prop := 3*a+b < 3 ∧ a+3*b < 3

def P5 (a b : ℝ) : Prop := P8 a b ∧ a+b ≤ Real.sqrt 5-1
def P5Strict (a b : ℝ) : Prop := P8Strict a b ∧ a+b < Real.sqrt 5-1

lemma p3_of_phi_le {a b : ℝ} (h : phi a b ≤ (425:ℝ)/256) : P3 a b := by
  have h₀ := tangent_le (u := 1/2) (v := 5/16) h (by norm_num [phi])
  have h₁ := tangent_le (u := 5/16) (v := 1/2) h (by norm_num [phi])
  have h₂ := tangent_le (u := 11/16) (v := 0) h (by norm_num [phi])
  have h₃ := tangent_le (u := 0) (v := 11/16) h (by norm_num [phi])
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma p3_of_phi_lt {a b : ℝ} (h : phi a b < (425:ℝ)/256) : P3Strict a b := by
  have h₀ := tangent_lt (u := 1/2) (v := 5/16) h (by norm_num [phi])
  have h₁ := tangent_lt (u := 5/16) (v := 1/2) h (by norm_num [phi])
  have h₂ := tangent_lt (u := 11/16) (v := 0) h (by norm_num [phi])
  have h₃ := tangent_lt (u := 0) (v := 11/16) h (by norm_num [phi])
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma p4_of_phi_le {a b : ℝ} (h : phi a b ≤ 2) : P4 a b := by
  have hh := tangent_le (u := 1/2) (v := 1/2) h (by norm_num [phi])
  dsimp [P4]; linarith

lemma p4_of_phi_lt {a b : ℝ} (h : phi a b < 2) : P4Strict a b := by
  have hh := tangent_lt (u := 1/2) (v := 1/2) h (by norm_num [phi])
  dsimp [P4Strict]; linarith

lemma p5_contact : phi ((Real.sqrt 5-1)/2) ((Real.sqrt 5-1)/2) = 5/2 := by
  have hh := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  dsimp [phi]; nlinarith

lemma p5_of_phi_le {a b : ℝ} (h : phi a b ≤ (5:ℝ)/2) : P5 a b := by
  have h₀ := tangent_le (u := 1) (v := 0) h (by norm_num [phi])
  have h₁ := tangent_le (u := 0) (v := 1) h (by norm_num [phi])
  have h₂ := tangent_le h p5_contact
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  by_contra hn
  have hmul := mul_pos hs (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith

lemma p5_of_phi_lt {a b : ℝ} (h : phi a b < (5:ℝ)/2) : P5Strict a b := by
  have h₀ := tangent_lt (u := 1) (v := 0) h (by norm_num [phi])
  have h₁ := tangent_lt (u := 0) (v := 1) h (by norm_num [phi])
  have h₂ := tangent_lt h p5_contact
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  by_contra hn
  have hmul := mul_nonneg hs (sub_nonneg.mpr (le_of_not_gt hn))
  nlinarith

lemma p3_coordinates {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P3 a b) :
    a ≤ 11/16 ∧ b ≤ 11/16 ∧ a+b ≤ 193/232 := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  exact ⟨by linarith, by linarith, by linarith⟩

lemma p3Strict_to_p3 {a b : ℝ} (h : P3Strict a b) : P3 a b :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩
lemma p5Strict_to_p5 {a b : ℝ} (h : P5Strict a b) : P5 a b :=
  ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.le⟩

lemma p4_to_p8 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P4 a b) : P8 a b := by
  dsimp [P4] at h
  exact ⟨by linarith, by linarith⟩
lemma p4Strict_to_p8Strict {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : P4Strict a b) : P8Strict a b := by
  dsimp [P4Strict] at h
  exact ⟨by linarith, by linarith⟩
lemma p3_to_p8Strict {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : P3 a b) : P8Strict a b := by
  have hc := p3_coordinates ha hb h
  apply p4Strict_to_p8Strict ha hb
  dsimp [P4Strict]; linarith [hc.2.2]

lemma p3_swap {a b : ℝ} (h : P3 a b) : P3 b a := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩
lemma p5_swap {a b : ℝ} (h : P5 a b) : P5 b a := by
  rcases h with ⟨⟨h₀,h₁⟩,h₂⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- A strict violation of the diamond bound is stable under moving the test point. -/
lemma strict_diamond_isOpen {n : ℕ} (S : Fin n → UnitSquare) :
    IsOpen {o : Point | ∀ i, P4Strict (alpha (S i) o) (beta (S i) o)} := by
  have hi (i : Fin n) : IsOpen {o : Point | P4Strict (alpha (S i) o) (beta (S i) o)} :=
    isOpen_lt ((alpha_continuous (S i)).add (beta_continuous (S i))) continuous_const
  simpa only [Set.setOf_forall] using isOpen_iInter_of_finite hi

end ThreeUnitSquaresInCircle.Unified
