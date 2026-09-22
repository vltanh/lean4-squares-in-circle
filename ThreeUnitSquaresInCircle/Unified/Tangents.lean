import ThreeUnitSquaresInCircle.Unified.Basic

/-!
# The three tangent bodies

The contact identity is shared; the constants are specific to the three packings.
`P3`, `P4`, and `P5` are predicates on NONNEGATIVE local center coordinates.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

def P3 (a b : ℝ) : Prop :=
  16*a + 13*b ≤ 193/16 ∧ 13*a + 16*b ≤ 193/16 ∧
  19*a + 8*b ≤ 209/16 ∧ 8*a + 19*b ≤ 209/16

def P3Strict (a b : ℝ) : Prop :=
  16*a + 13*b < 193/16 ∧ 13*a + 16*b < 193/16 ∧
  19*a + 8*b < 209/16 ∧ 8*a + 19*b < 209/16

def P4 (a b : ℝ) : Prop := a + b ≤ 1

def P4Strict (a b : ℝ) : Prop := a + b < 1

def Octagon (a b : ℝ) : Prop := 3*a + b ≤ 3 ∧ a + 3*b ≤ 3

def OctagonStrict (a b : ℝ) : Prop := 3*a + b < 3 ∧ a + 3*b < 3

def P5 (a b : ℝ) : Prop := Octagon a b ∧ a + b ≤ Real.sqrt 5 - 1

def P5Strict (a b : ℝ) : Prop :=
  OctagonStrict a b ∧ a + b < Real.sqrt 5 - 1

def CenterBody (P : ℝ → ℝ → Prop) (S : UnitSquare) (o : Point) : Prop :=
  P (alpha S o) (beta S o)

/-- Exact supporting-line identity; the discarded term is a sum of squares. -/
theorem tangent_identity (a b A B : ℝ) :
    phi a b - phi A B =
      (2*A+1)*(a-A) + (2*B+1)*(b-B) + (a-A)^2 + (b-B)^2 := by
  unfold phi
  ring

theorem tangent_le {a b A B q : ℝ} (hc : phi A B = q) (h : phi a b ≤ q) :
    (2*A+1)*(a-A) + (2*B+1)*(b-B) ≤ 0 := by
  have he := tangent_identity a b A B
  rw [hc] at he
  nlinarith [sq_nonneg (a-A), sq_nonneg (b-B)]

theorem tangent_lt {a b A B q : ℝ} (hc : phi A B = q) (h : phi a b < q) :
    (2*A+1)*(a-A) + (2*B+1)*(b-B) < 0 := by
  have he := tangent_identity a b A B
  rw [hc] at he
  nlinarith [sq_nonneg (a-A), sq_nonneg (b-B)]

theorem phi_P3 {a b : ℝ} (h : phi a b ≤ 425/256) : P3 a b := by
  have h₁ := tangent_le (A := (1/2 : ℝ)) (B := (5/16 : ℝ))
    (by norm_num [phi]) h
  have h₂ := tangent_le (A := (5/16 : ℝ)) (B := (1/2 : ℝ))
    (by norm_num [phi]) h
  have h₃ := tangent_le (A := (11/16 : ℝ)) (B := (0 : ℝ))
    (by norm_num [phi]) h
  have h₄ := tangent_le (A := (0 : ℝ)) (B := (11/16 : ℝ))
    (by norm_num [phi]) h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem phi_P3Strict {a b : ℝ} (h : phi a b < 425/256) : P3Strict a b := by
  have h₁ := tangent_lt (A := (1/2 : ℝ)) (B := (5/16 : ℝ))
    (by norm_num [phi]) h
  have h₂ := tangent_lt (A := (5/16 : ℝ)) (B := (1/2 : ℝ))
    (by norm_num [phi]) h
  have h₃ := tangent_lt (A := (11/16 : ℝ)) (B := (0 : ℝ))
    (by norm_num [phi]) h
  have h₄ := tangent_lt (A := (0 : ℝ)) (B := (11/16 : ℝ))
    (by norm_num [phi]) h
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem phi_P4 {a b : ℝ} (h : phi a b ≤ 2) : P4 a b := by
  have ht := tangent_le (A := (1/2 : ℝ)) (B := (1/2 : ℝ))
    (by norm_num [phi]) h
  dsimp [P4]
  linarith

theorem phi_P4Strict {a b : ℝ} (h : phi a b < 2) : P4Strict a b := by
  have ht := tangent_lt (A := (1/2 : ℝ)) (B := (1/2 : ℝ))
    (by norm_num [phi]) h
  dsimp [P4Strict]
  linarith

private theorem diagonal5_contact :
    phi ((Real.sqrt 5 - 1)/2) ((Real.sqrt 5 - 1)/2) = 5/2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold phi
  nlinarith

theorem phi_P5 {a b : ℝ} (h : phi a b ≤ 5/2) : P5 a b := by
  have hx := tangent_le (A := (1 : ℝ)) (B := (0 : ℝ))
    (by norm_num [phi]) h
  have hy := tangent_le (A := (0 : ℝ)) (B := (1 : ℝ))
    (by norm_num [phi]) h
  have hd := tangent_le diagonal5_contact h
  have hs : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  by_contra hn
  have ht : 0 < Real.sqrt 5 * (a+b-(Real.sqrt 5-1)) :=
    mul_pos hp (sub_pos.2 (lt_of_not_ge hn))
  nlinarith

theorem phi_P5Strict {a b : ℝ} (h : phi a b < 5/2) : P5Strict a b := by
  have hx := tangent_lt (A := (1 : ℝ)) (B := (0 : ℝ))
    (by norm_num [phi]) h
  have hy := tangent_lt (A := (0 : ℝ)) (B := (1 : ℝ))
    (by norm_num [phi]) h
  have hd := tangent_lt diagonal5_contact h
  have hs : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  by_contra hn
  have ht := mul_nonneg hp (sub_nonneg.2 (le_of_not_gt hn))
  nlinarith

theorem P3Strict.le {a b : ℝ} (h : P3Strict a b) : P3 a b :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem P5Strict.le {a b : ℝ} (h : P5Strict a b) : P5 a b :=
  ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.le⟩

theorem P3.sum_le {a b : ℝ} (h : P3 a b) : a+b ≤ 193/232 := by
  linarith [h.1, h.2.1]

theorem P3.coord_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P3 a b) :
    a ≤ 11/16 ∧ b ≤ 11/16 := by
  constructor <;> linarith [h.2.2.1, h.2.2.2]

theorem P3.symm {a b : ℝ} (h : P3 a b) : P3 b a := by
  rcases h with ⟨h₁,h₂,h₃,h₄⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem P4.octagon {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P4 a b) :
    Octagon a b := by
  dsimp [P4] at h
  constructor <;> linarith

theorem P4Strict.octagonStrict {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : P4Strict a b) : OctagonStrict a b := by
  dsimp [P4Strict] at h
  constructor <;> linarith

theorem P3.octagonStrict {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P3 a b) :
    OctagonStrict a b := by
  apply P4Strict.octagonStrict ha hb
  have hs := h.sum_le
  dsimp [P4Strict]
  linarith

end ThreeUnitSquaresInCircle.Unified
