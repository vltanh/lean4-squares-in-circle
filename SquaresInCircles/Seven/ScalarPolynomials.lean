import SquaresInCircles.Seven.TaylorBounds

/-!
# Whole-interval polynomial signs for the remaining axial/side estimates

The coefficient lists are exact rational data. Each list is connected to its
polynomial by a `ring` identity, and its signs by `norm_num`. These are not
sampled values, interval boxes, native computations, or external proof flags.
-/
noncomputable section
open scoped BigOperators
namespace SquaresInCircles.Seven

namespace WholeInterval

def basis (n : ℕ) (i : Fin (n+1)) (x : ℝ) : ℝ :=
  (n.choose i.val : ℝ)*x^i.val*(1-x)^(n-i.val)

lemma basis_nonneg (n : ℕ) (i : Fin (n+1)) {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) : 0 ≤ basis n i x := by
  have h0 := hx.1
  have h1 := sub_nonneg.mpr hx.2
  unfold basis
  positivity

lemma positive_sum (n : ℕ) (c : Fin (n+1) → ℝ)
    (hc : ∀ i,0 < c i) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    0 < ∑ i,c i*basis n i x := by
  have hnon (i : Fin (n+1)) : 0 ≤ c i*basis n i x :=
    mul_nonneg (hc i).le (basis_nonneg n i hx)
  by_cases he : x = 1
  · subst x
    have hp : 0 < c (Fin.last n)*basis n (Fin.last n) 1 := by
      simpa [basis] using hc (Fin.last n)
    exact hp.trans_le (Finset.single_le_sum (fun i _ => hnon i)
      (Finset.mem_univ (Fin.last n)))
  · have h1 : 0 < 1-x := by linarith [hx.2]
    have hp : 0 < c 0*basis n 0 x := by
      simp only [basis,Fin.val_zero,Nat.choose_zero,Nat.cast_one,pow_zero,
        one_mul,mul_one,Nat.sub_zero]
      exact mul_pos (hc 0) (pow_pos h1 n)
    exact hp.trans_le (Finset.single_le_sum (fun i _ => hnon i)
      (Finset.mem_univ (0 : Fin (n+1))))
end WholeInterval

namespace TaylorPoly

def sin7 (z : ℝ) : ℝ := z-z^3/6+z^5/120-z^7/5040
def sin5 (z : ℝ) : ℝ := z-z^3/6+z^5/120
def cos6 (z : ℝ) : ℝ := 1-z^2/2+z^4/24-z^6/720
def cos4 (z : ℝ) : ℝ := 1-z^2/2+z^4/24

lemma sin7_le {z : ℝ} (hz : 0 ≤ z) : sin7 z ≤ Real.sin z := sin_lower_seven hz
lemma sin_le_sin5 {z : ℝ} (hz : 0 ≤ z) : Real.sin z ≤ sin5 z := sin_upper_five hz
lemma cos6_le {z : ℝ} (hz : 0 ≤ z) : cos6 z ≤ Real.cos z := cos_lower_six hz
lemma cos_le_cos4 {z : ℝ} (hz : 0 ≤ z) : Real.cos z ≤ cos4 z := cos_upper_four hz
end TaylorPoly

open WholeInterval TaylorPoly

def axialSmallQ (z : ℝ) : ℝ :=
  1/5-7*z/16+7*z^2/30+7*z^3/192-z^4/40-7*z^5/5760+23*z^6/25200

private def axialSmallCoeffs : Fin 10 → ℝ :=
  ![1/5,3383/23040,112159/1105920,24281447/377487360,
    9018523/251658240,55451924077/3478923509760,
    40097895347/9277129359360,1239527599/3092376453120,
    23367206479/6957847019520,9435381281/773094113280]

lemma axialSmallQ_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 35/32) : 0 < axialSmallQ z := by
  let x := (32/35)*z
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 10) : 0 < axialSmallCoeffs i := by
    fin_cases i <;> norm_num [axialSmallCoeffs]
  have hp := positive_sum 9 axialSmallCoeffs hc hx
  have he : axialSmallQ z = ∑ i,axialSmallCoeffs i*basis 9 i x := by
    simp [axialSmallQ,axialSmallCoeffs,basis,Fin.sum_univ_succ,x]
    ring
  rw [he]
  exact hp

lemma axialSmall_identity (z : ℝ) :
    z*axialSmallQ z = sin7 z-7/8+(7/8-(4/5)*z)*cos6 z := by
  dsimp [axialSmallQ,sin7,cos6]
  ring

def axialLargeP (z : ℝ) : ℝ :=
  sin7 z-7/8+(7/8-(4/5)*z)*cos4 z

private def axialLargeCoeffs : Fin 8 → ℝ :=
  ![66047668967/4947802324992,738121569901/37881611550720,
    33625345261/1183800360960,209075098301/5179126579200,
    3928166009/70808371200,12772753379/173480509440,
    64027903/677658240,1949725657/16602626880]

lemma axialLargeP_pos {z : ℝ} (hz : 35/32 ≤ z ∧ z ≤ 11/7) : 0 < axialLargeP z := by
  let x := (224/107)*(z-35/32)
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 8) : 0 < axialLargeCoeffs i := by
    fin_cases i <;> norm_num [axialLargeCoeffs]
  have hp := positive_sum 7 axialLargeCoeffs hc hx
  have he : axialLargeP z = ∑ i,axialLargeCoeffs i*basis 7 i x := by
    simp [axialLargeP,axialLargeCoeffs,basis,sin7,cos4,Fin.sum_univ_succ,x]
    ring
  rw [he]
  exact hp

/-- Scalar appendix 3, expressed in a positive basis on the whole interval. -/
def shortSideH (z : ℝ) : ℝ :=
  26/75-(653/300)*z+(23/45)*z^2+(349/720)*z^3
    -(47/900)*z^4-(1069/21600)*z^5-(13/37800)*z^6

private def shortSideCoeffs : Fin 7 → ℝ :=
  ![26/75,3091/10800,11017/48600,523261/3110400,
    3882011/34992000,55351163/1007769600,1001149/3527193600]

lemma shortSideH_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/6) : 0 < shortSideH z := by
  let x := 6*z
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 7) : 0 < shortSideCoeffs i := by
    fin_cases i <;> norm_num [shortSideCoeffs]
  have hp := positive_sum 6 shortSideCoeffs hc hx
  have he : shortSideH z = ∑ i,shortSideCoeffs i*basis 6 i x := by
    simp [shortSideH,shortSideCoeffs,basis,Fin.sum_univ_succ,x]
    ring
  rw [he]
  exact hp

/-- A polynomial lower bound for the large-angle axial-target profile. -/
def largeAxialP (z : ℝ) : ℝ :=
  1+157/375-(4/5)*z+cos6 z-(51/20)*(cos4 (z/2)-sin7 (z/2))

private def largeAxialCoeffs : Fin 8 → ℝ :=
  ![27834859/5225472000,21646979107/329204736000,
    85094698273/768144384000,83663391929/597445632000,
    650018406713/4182119424000,224217116981/1394039808000,
    1222825127771/7589772288000,8516973787387/53128406016000]

lemma largeAxialP_pos {z : ℝ} (hz : 1/3 ≤ z ∧ z ≤ 11/7) : 0 < largeAxialP z := by
  let x := (21/26)*(z-1/3)
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 8) : 0 < largeAxialCoeffs i := by
    fin_cases i <;> norm_num [largeAxialCoeffs]
  have hp := positive_sum 7 largeAxialCoeffs hc hx
  have he : largeAxialP z = ∑ i,largeAxialCoeffs i*basis 7 i x := by
    simp [largeAxialP,largeAxialCoeffs,basis,sin7,cos6,cos4,Fin.sum_univ_succ,x]
    ring
  rw [he]
  exact hp

def smallAxialL (z : ℝ) : ℝ := cos6 z-55/168-(4/5)*z+(873/250)*sin7 z

def smallAxialU (z : ℝ) : ℝ :=
  1189/800-(27/20)*cos6 z+(27/10)*cos4 z*sin5 z
    +(249/200)*(z^2-z^4/3+2*z^6/45)-(319/200)*sin7 z

private def smallAxialCoeffs : Fin 15 → ℝ :=
  ![13553/1411200,72827/7056000,393747163/34398000000,
    2710739309/206388000000,9910498733/638512875000,
    153072314621/8172964800000,47296571468413/2068781715000000,
    3708166534047959/132402029760000000,
    188854262621881/5516751240000000,6257753867831/150456852000000,
    6998517462046433/139642765762500000,
    48606823214392757/812467000800000000,
    29832818108969789/421857865800000000,
    34918908326684453/421857865800000000,
    80964059146525129/843715731600000000]

lemma smallAxial_discriminant_pos {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1/3) :
    0 < (smallAxialL z)^2-(13/4)*smallAxialU z := by
  let x := 3*z
  have hx : 0 ≤ x ∧ x ≤ 1 := by dsimp [x]; constructor <;> linarith
  have hc (i : Fin 15) : 0 < smallAxialCoeffs i := by
    fin_cases i <;> norm_num [smallAxialCoeffs]
  have hp := positive_sum 14 smallAxialCoeffs hc hx
  have he : (smallAxialL z)^2-(13/4)*smallAxialU z =
      ∑ i,smallAxialCoeffs i*basis 14 i x := by
    simp [smallAxialL,smallAxialU,smallAxialCoeffs,basis,
      sin7,sin5,cos6,cos4,Fin.sum_univ_succ,x]
    ring
  rw [he]
  exact hp

end SquaresInCircles.Seven
