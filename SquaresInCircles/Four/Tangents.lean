import SquaresInCircles.Common.Tangents

/-!
# The contact diamond

The tangent to `phi = 2` at `(1/2, 1/2)` bounds every square of a four-square
packing by `a + b ≤ 1`; `P4Strict` is the strict version.
-/
noncomputable section
namespace SquaresInCircles

def P4 (a b : ℝ) : Prop := a+b ≤ 1
def P4Strict (a b : ℝ) : Prop := a+b < 1

lemma p4_of_phi_le {a b : ℝ} (h : phi a b ≤ 2) : P4 a b := by
  have hh := tangent_le (u := 1/2) (v := 1/2) h (by norm_num [phi])
  dsimp [P4]; linarith

lemma p4_of_phi_lt {a b : ℝ} (h : phi a b < 2) : P4Strict a b := by
  have hh := tangent_lt (u := 1/2) (v := 1/2) h (by norm_num [phi])
  dsimp [P4Strict]; linarith

lemma p4Strict_to_p8Strict {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : P4Strict a b) : P8Strict a b := by
  dsimp [P4Strict] at h
  exact ⟨by linarith, by linarith⟩

end SquaresInCircles
