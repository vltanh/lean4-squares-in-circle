import SquaresInCircles.Common.RectangleArcs

/-! For four squares, a slightly smaller auxiliary radius makes every exterior
arc strictly longer than a quarter-circle, including the axial equality cases. -/
noncomputable section
open Set
namespace SquaresInCircles

lemma near_corner_sq_lt_half {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpos : 0 < a+b) (hs : a+b < 1) : (a-1/2)^2+(b-1/2)^2 < 1/2 := by
  have hh := mul_pos hpos (sub_pos.mpr hs)
  nlinarith [mul_nonneg ha hb]

lemma abs_center_sum_pos (S : UnitSquare) (o : Point) (hne : S.center ≠ o) :
    0 < alpha S o+beta S o := by
  have hsub : sub S.center o ≠ (0,0) := by
    intro hh
    apply hne
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    apply Prod.ext <;> dsimp [sub] at * <;> linarith
  have hp := normSq_pos_of_ne hsub
  have he := frame_norm S (sub S.center o)
  rw [frame_centerX,frame_centerY] at he
  have ha := alpha_nonneg S o
  have hb := beta_nonneg S o
  have hxa : (alpha S o)^2=(localX S o)^2 := sq_abs _
  have hya : (beta S o)^2=(localY S o)^2 := sq_abs _
  nlinarith

lemma finite_between {ι : Type*} (s : Finset ι) (f : ι → ℝ) {L U : ℝ}
    (hLU : L < U) (hf : ∀ i ∈ s, f i < U) :
    ∃ r : ℝ, L < r ∧ r < U ∧ ∀ i ∈ s, f i < r := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      obtain ⟨r,hr₀,hr₁⟩ := exists_between hLU
      exact ⟨r,hr₀,hr₁,by simp⟩
  | @insert i s hi ih =>
      intro hf
      obtain ⟨r,hrL,hrU,hrf⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hm : max r (f i) < U := max_lt hrU (hf i (Finset.mem_insert_self _ _))
      obtain ⟨r',hr'₀,hr'₁⟩ := exists_between hm
      have hrr : r < r' := (le_max_left _ _).trans_lt hr'₀
      refine ⟨r',hrL.trans hrr,hr'₁,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (le_max_right _ _).trans_lt hr'₀
      · exact (hrf j hj).trans hrr

lemma common_four_radius {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hpos : ∀ i, 0 < a i+b i) (hs : ∀ i, a i+b i < 1) :
    ∃ r : ℝ, 1/2 < r ∧ r < halfDiagonal ∧
      ∀ i, (a i-1/2)^2+(b i-1/2)^2 < r^2 := by
  have hU : ∀ i, Real.sqrt ((a i-1/2)^2+(b i-1/2)^2) < halfDiagonal := by
    intro i
    have hn : 0 ≤ (a i-1/2)^2+(b i-1/2)^2 := by positivity
    have he := Real.sq_sqrt hn
    have hh := near_corner_sq_lt_half (ha i) (hb i) (hpos i) (hs i)
    nlinarith [Real.sqrt_nonneg ((a i-1/2)^2+(b i-1/2)^2),halfDiagonal_sq,halfDiagonal_pos]
  obtain ⟨r,hrL,hrU,hrf⟩ := finite_between Finset.univ
    (fun i => Real.sqrt ((a i-1/2)^2+(b i-1/2)^2))
    (show (1/2:ℝ) < halfDiagonal by nlinarith [halfDiagonal_sq,halfDiagonal_pos])
    (fun i _ => hU i)
  refine ⟨r,hrL,hrU,?_⟩
  intro i
  have hh := hrf i (Finset.mem_univ _)
  have he := Real.sq_sqrt (show 0 ≤ (a i-1/2)^2+(b i-1/2)^2 by positivity)
  nlinarith [Real.sqrt_nonneg ((a i-1/2)^2+(b i-1/2)^2)]

lemma four_rectangle_length {a b r : ℝ} (ha : 1/2 ≤ a) (hb : 0 ≤ b)
    (hs : a+b < 1) (hr0 : 1/2 < r) (hr1 : r < halfDiagonal)
    (_hcorner : (a-1/2)^2+(b-1/2)^2 < r^2) :
    Real.pi/2 < rectangleHi a b r-rectangleLo b r := by
  have hr : 0 < r := by linarith
  have hr2 : r^2 < 1/2 := by nlinarith [halfDiagonal_sq,halfDiagonal_pos]
  have hx0 : 0 ≤ (a-1/2)/r := div_nonneg (by linarith) hr.le
  have hx1 : (a-1/2)/r < 1 := (div_lt_one hr).mpr (by nlinarith [sq_nonneg (b-1/2)])
  have hy : (b-1/2)/r ∈ Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hr).mpr
      nlinarith [sq_nonneg (a-1/2)]
    · apply (div_le_iff₀ hr).mpr
      nlinarith [sq_nonneg (a-1/2)]
  have hsum : (a-1/2)/r+(b-1/2)/r < 0 := by
    rw [← add_div]
    exact div_neg_of_neg_of_pos (by linarith) hr
  have hf := arcsin_sum_lt_zero ⟨by linarith,hx1.le⟩ hy hsum
  have hfirst : Real.pi/2 < Real.arccos ((a-1/2)/r)-Real.arcsin ((b-1/2)/r) := by
    dsimp [Real.arccos]; linarith
  have hsecond : Real.pi/2 < Real.arcsin ((b+1/2)/r)-Real.arcsin ((b-1/2)/r) := by
    by_cases ht : r ≤ b+1/2
    · have he := Real.arcsin_of_one_le ((le_div_iff₀ hr).mpr (by linarith : 1*r ≤ b+1/2))
      rw [he]
      have hx := Real.arcsin_nonneg.mpr hx0
      dsimp [Real.arccos] at hfirst
      linarith
    · have hbhalf : b < 1/2 := by nlinarith [halfDiagonal_sq,halfDiagonal_pos]
      have hu : (b+1/2)/r ∈ Icc (0:ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith) hr.le
        · exact (div_le_one hr).mpr (le_of_lt (lt_of_not_ge ht))
      have hv : (1/2-b)/r ∈ Icc (0:ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith) hr.le
        · exact (div_le_one hr).mpr (by linarith)
      have hsq : 1 < ((b+1/2)/r)^2+((1/2-b)/r)^2 := by
        rw [div_pow,div_pow,← add_div]
        apply (lt_div_iff₀ (sq_pos_of_pos hr)).mpr
        nlinarith [sq_nonneg b]
      have hh := arcsin_sum_gt_half_pi hu hv hsq
      have he : (b-1/2)/r = -((1/2-b)/r) := by ring
      rw [he,Real.arcsin_neg]
      linarith
  have hh : Real.pi/2+Real.arcsin ((b-1/2)/r) <
      min (Real.arccos ((a-1/2)/r)) (Real.arcsin ((b+1/2)/r)) :=
    lt_min (by linarith) (by linarith)
  dsimp [rectangleHi,rectangleLo]
  linarith

lemma four_exterior_arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {r : ℝ} (hsort : C.b ≤ C.a) (hs : C.a+C.b < 1)
    (hout : ¬ openSquare S o) (hr0 : 1/2 < r) (hr1 : r < halfDiagonal)
    (hcorner : (C.a-1/2)^2+(C.b-1/2)^2 < r^2) :
    ∃ A : OpenArc o r {p | openSquare S p}, Real.pi/4 < A.halfWidth := by
  have ha := C.exterior hsort hout
  have hb := C.nonneg.2
  have hr : 0 < r := by linarith
  have hx : (C.a-1/2)/r ∈ Ico (0:ℝ) 1 := by
    refine ⟨div_nonneg (by linarith) hr.le,(div_lt_one hr).mpr ?_⟩
    nlinarith [sq_nonneg (C.b-1/2)]
  have hy : (C.b-1/2)/r ∈ Icc (-1:ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hr).mpr
      nlinarith [sq_nonneg (C.a-1/2)]
    · apply (div_le_iff₀ hr).mpr
      nlinarith [sq_nonneg (C.a-1/2)]
  have hc : ((C.a-1/2)/r)^2+((C.b-1/2)/r)^2 < 1 := by
    rw [div_pow,div_pow,← add_div]
    exact (div_lt_one (sq_pos_of_pos hr)).mpr hcorner
  have hfar : r < C.a+1/2 := by nlinarith [halfDiagonal_sq,halfDiagonal_pos]
  obtain ⟨A,hA⟩ := exterior_arc_from_length C hr hfar hx hy hc
    (show 0 < Real.pi/2 by positivity)
    (four_rectangle_length ha hb hs hr0 hr1 hcorner)
  exact ⟨A,by linarith⟩

end SquaresInCircles
