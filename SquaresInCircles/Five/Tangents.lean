import SquaresInCircles.Common.Tangents

/-!
# The contact 12-gon

Tangents to `phi = 5/2` at `(1, 0)`, `(0, 1)` and `((√5-1)/2, (√5-1)/2)` bound
every square of a five-square packing; `P5Strict` is the strict version.
-/
noncomputable section
namespace SquaresInCircles

def P5 (a b : ℝ) : Prop := P8 a b ∧ a+b ≤ Real.sqrt 5-1
def P5Strict (a b : ℝ) : Prop := P8Strict a b ∧ a+b < Real.sqrt 5-1

lemma p5_contact : phi ((Real.sqrt 5-1)/2) ((Real.sqrt 5-1)/2) = 5/2 := by
  have hh := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  dsimp [phi]; linarith

lemma p5_of_phi_le {a b : ℝ} (h : phi a b ≤ (5:ℝ)/2) : P5 a b := by
  have h₀ := tangent_le (u := 1) (v := 0) h (by norm_num [phi])
  have h₁ := tangent_le (u := 0) (v := 1) h (by norm_num [phi])
  have h₂ := tangent_le h p5_contact
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  by_contra hn
  have hmul := mul_pos hs (sub_pos.mpr (lt_of_not_ge hn))
  linarith

lemma p5_of_phi_lt {a b : ℝ} (h : phi a b < (5:ℝ)/2) : P5Strict a b := by
  have h₀ := tangent_lt (u := 1) (v := 0) h (by norm_num [phi])
  have h₁ := tangent_lt (u := 0) (v := 1) h (by norm_num [phi])
  have h₂ := tangent_lt h p5_contact
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  by_contra hn
  have hmul := mul_nonneg hs (sub_nonneg.mpr (le_of_not_gt hn))
  linarith

lemma p5Strict_to_p5 {a b : ℝ} (h : P5Strict a b) : P5 a b :=
  ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.le⟩

lemma p5_swap {a b : ℝ} (h : P5 a b) : P5 b a := by
  rcases h with ⟨⟨h₀,h₁⟩,h₂⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

end SquaresInCircles
