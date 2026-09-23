import SquaresInCircles.Common.Tangents

/-!
# The contact 16-gon

Tangents to `phi = 425/256` at `(1/2, 5/16)`, `(11/16, 0)` and their swaps bound
every square of a three-square packing; `P3Strict` is the strict version.
-/
noncomputable section
namespace SquaresInCircles

def P3 (a b : ℝ) : Prop :=
  16*a+13*b ≤ 193/16 ∧ 13*a+16*b ≤ 193/16 ∧
  19*a+8*b ≤ 209/16 ∧ 8*a+19*b ≤ 209/16

def P3Strict (a b : ℝ) : Prop :=
  16*a+13*b < 193/16 ∧ 13*a+16*b < 193/16 ∧
  19*a+8*b < 209/16 ∧ 8*a+19*b < 209/16

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

lemma p3_coordinates {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : P3 a b) :
    a ≤ 11/16 ∧ b ≤ 11/16 ∧ a+b ≤ 193/232 := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  exact ⟨by linarith, by linarith, by linarith⟩

lemma p3Strict_to_p3 {a b : ℝ} (h : P3Strict a b) : P3 a b :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

lemma p3_swap {a b : ℝ} (h : P3 a b) : P3 b a := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma p3Strict_swap {a b : ℝ} (h : P3Strict a b) : P3Strict b a := by
  rcases h with ⟨h₀,h₁,h₂,h₃⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end SquaresInCircles
