import SquaresInCircles.Seven.PairModel

/-! Periodic support identities for the canonical separating-axis table. -/
noncomputable section
namespace SquaresInCircles.Seven

lemma support_three_half_sub (a b d : ℝ) :
    support a b (3*Real.pi/2-d)=
      -a*Real.sin d-b*Real.cos d+(|Real.sin d|+|Real.cos d|)/2 := by
  have he : 3*Real.pi/2-d=Real.pi+(Real.pi/2-d) := by ring
  rw [he]
  simp only [support,Real.cos_add,Real.sin_add,Real.cos_pi,Real.sin_pi,
    Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
    zero_mul,mul_zero,zero_add,sub_zero,neg_one_mul,one_mul,abs_neg]
  ring

lemma support_two_pi_sub (a b d : ℝ) :
    support a b (2*Real.pi-d)=
      a*Real.cos d-b*Real.sin d+(|Real.cos d|+|Real.sin d|)/2 := by
  simp only [support,Real.cos_sub,Real.sin_sub,Real.cos_two_pi,Real.sin_two_pi,
    one_mul,zero_mul,zero_add,zero_sub,abs_neg]
  ring

end SquaresInCircles.Seven
