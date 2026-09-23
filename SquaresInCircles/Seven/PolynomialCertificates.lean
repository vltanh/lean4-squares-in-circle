import Mathlib

/-!
# Exact polynomial certificates from the analytical manuscript

No interval search or external computation is part of these statements.
Every polynomial identity is checked by `ring`; all coefficient inequalities
are rational arithmetic checked by `norm_num`. Bernstein positivity proves a
whole interval at once, not a finite set of sample points.
-/
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Seven

private def bernstein (n : ℕ) (i : Fin (n+1)) (x : ℝ) : ℝ :=
  (n.choose i.val : ℝ) * x^i.val * (1-x)^(n-i.val)

private lemma bernstein_nonneg (n : ℕ) (i : Fin (n+1)) {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) : 0 ≤ bernstein n i x := by
  have hx0 := hx.1
  have hx1 : 0 ≤ 1-x := sub_nonneg.mpr hx.2
  unfold bernstein
  positivity

private lemma positive_bernstein_sum (n : ℕ) (c : Fin (n+1) → ℝ)
    (hc : ∀ i, 0 < c i) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    0 < ∑ i, c i * bernstein n i x := by
  have hnon (i : Fin (n+1)) : 0 ≤ c i * bernstein n i x :=
    mul_nonneg (hc i).le (bernstein_nonneg n i hx)
  by_cases h : x = 1
  · subst x
    have ht : 0 < c (Fin.last n) * bernstein n (Fin.last n) 1 := by
      simpa [bernstein] using hc (Fin.last n)
    exact ht.trans_le (Finset.single_le_sum (fun i _ => hnon i)
      (Finset.mem_univ (Fin.last n)))
  · have hx' : 0 < 1-x := by rcases hx with ⟨hl,hu⟩; linarith
    have ht : 0 < c 0 * bernstein n 0 x := by
      have he : bernstein n 0 x = (1-x)^n := by simp [bernstein]
      rw [he]
      exact mul_pos (hc 0) (pow_pos hx' n)
    exact ht.trans_le (Finset.single_le_sum (fun i _ => hnon i)
      (Finset.mem_univ (0 : Fin (n+1))))

/-- Scalar appendix 4.1. -/
def axialPairPolynomial (z : ℝ) : ℝ :=
  17/105 + z/20 - z^2/4 + 7*z^3/60 - z^5/160

private def axialPairCoefficients : Fin 6 → ℝ :=
  ![17/105, 3631/21000, 12907/84000, 502669/4200000,
    22711/262500, 20033129/336000000]

lemma axialPairPolynomial_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 11/10) :
    0 < axialPairPolynomial z := by
  let x := 10*z/11
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 6) : 0 < axialPairCoefficients i := by
    fin_cases i <;> norm_num [axialPairCoefficients]
  have hp := positive_bernstein_sum 5 axialPairCoefficients hc hx
  have hid : axialPairPolynomial z =
      ∑ i : Fin 6, axialPairCoefficients i * bernstein 5 i x := by
    simp [axialPairPolynomial, axialPairCoefficients, bernstein,
      Fin.sum_univ_succ, x]
    ring
  rw [hid]
  exact hp

/-- Scalar appendix 4.2, the numerator of an axial-circle derivative comparison. -/
def axialRatioPolynomial (X : ℝ) : ℝ :=
  -500*X^5+800*X^4+1705*X^3-3900*X^2+3120*X-1872

private def axialRatioCoefficients : Fin 6 → ℝ :=
  ![2992/25, 16676/125, 138343/1000, 423899/3200, 18151/160, 20113/256]

lemma axialRatioPolynomial_pos {X : ℝ} (hX : 8/5 ≤ X ∧ X ≤ 7/4) :
    0 < axialRatioPolynomial X := by
  let x := (20/3)*(X-8/5)
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 6) : 0 < axialRatioCoefficients i := by
    fin_cases i <;> norm_num [axialRatioCoefficients]
  have hp := positive_bernstein_sum 5 axialRatioCoefficients hc hx
  have hid : axialRatioPolynomial X =
      ∑ i : Fin 6, axialRatioCoefficients i * bernstein 5 i x := by
    simp [axialRatioPolynomial, axialRatioCoefficients, bernstein,
      Fin.sum_univ_succ, x]
    ring
  rw [hid]
  exact hp

/-- The degree-eleven discriminant polynomial in scalar appendix 6. -/
def radialPolynomial (z : ℝ) : ℝ :=
  201/2000 - (201353/7098000)*z - (3091/21840)*z^2
  - (1571239/14196000)*z^3 - (23103/7280000)*z^4
  + (977419/182520000)*z^5 - (13/6300)*z^6
  - (364297/196560000)*z^7 + z^8/90720 + z^9/8640 - z^11/518400

private def radialCoefficients : Fin 12 → ℝ :=
  ![201/2000, 61767947/624624000, 160355527/1665664000,
    22183121153/239855616000, 1341122208527/15350759424000,
    44622066127207/552627339264000, 23358801914587/322365947904000,
    4410162763554631/70736299425792000, 1523041486356419/30315556896768000,
    4524018740302909/125753421201408000, 406318644428659/20958903533568000,
    125352005285647/418089296461824000]

/-- A single Bernstein identity replaces the manuscript's derivative comparison. -/
lemma radialPolynomial_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 5/8) :
    0 < radialPolynomial z := by
  let x := 8*z/5
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 12) : 0 < radialCoefficients i := by
    fin_cases i <;> norm_num [radialCoefficients]
  have hp := positive_bernstein_sum 11 radialCoefficients hc hx
  have hid : radialPolynomial z =
      ∑ i : Fin 12, radialCoefficients i * bernstein 11 i x := by
    simp [radialPolynomial, radialCoefficients, bernstein,
      Fin.sum_univ_succ, x]
    ring
  rw [hid]
  exact hp

def radialB (z : ℝ) : ℝ :=
  67*z/1000-z^2/4+73*z^3/600+z^4/48-733*z^5/120000-z^6/1440

def radialL (z : ℝ) : ℝ :=
  (15/52)*(z-z^3/6)-(z^2/2-z^4/24+z^6/720)

def radialK (z : ℝ) : ℝ := (15/52+1/42)*(z-z^3/6)

def radialE (z v : ℝ) : ℝ :=
  radialB z+v*radialL z+v^2*radialK z+(6/25)*(z-5*v/4)^2

lemma radial_discriminant_identity (z : ℝ) :
    4*(radialK z+3/8)*(radialB z+(6/25)*z^2)
      -(radialL z-(3/5)*z)^2 = z*radialPolynomial z := by
  unfold radialB radialL radialK radialPolynomial
  ring

lemma radial_completion (z v : ℝ) :
    4*(radialK z+3/8)*radialE z v =
      (2*(radialK z+3/8)*v+(radialL z-(3/5)*z))^2+z*radialPolynomial z := by
  rw [← radial_discriminant_identity]
  unfold radialE
  ring

/-- The final polynomial lower bound is positive for every real v. -/
theorem radialE_pos {z : ℝ} (hz : 0 < z ∧ z ≤ 5/8) (v : ℝ) :
    0 < radialE z v := by
  have hm := mul_nonneg hz.1.le (show 0 ≤ 1-z^2 by nlinarith)
  have ht : 0 < z-z^3/6 := by nlinarith
  have hK : 0 < radialK z := by
    unfold radialK
    exact mul_pos (by norm_num) ht
  have hp := radialPolynomial_pos ⟨hz.1.le,hz.2⟩
  have hprod := mul_pos hz.1 hp
  have hid := radial_completion z v
  have hsq := sq_nonneg (2*(radialK z+3/8)*v+(radialL z-(3/5)*z))
  by_contra hn
  have hnon : 4*(radialK z+3/8)*radialE z v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hn)
  linarith

end SquaresInCircles.Seven
