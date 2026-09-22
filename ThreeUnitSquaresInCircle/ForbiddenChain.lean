import ThreeUnitSquaresInCircle.AxisSelection

/-! The geometric forbidden-chain estimate, in the Euclidean coordinate norm.
Compiles against Lean 4.34.0 / mathlib v4.34.0. -/
noncomputable section
namespace ThreeUnitSquaresInCircle.Cert
open RatData

/-- Geometric version of the algebraic center bound, for a single square. -/
lemma square_center_bound (S : UnitSquare) (c : Point) (R : ℝ)
    (hdisk : ∀ j : Fin 4, normSq (add c (rotate S (localVertex j))) ≤ R^2)
    (hsmall : R^2 ≤ targetSq) : Real.sqrt (normSq c) ≤ 11/16 := by
  let X : ℝ := S.cosine*c.1+S.sine*c.2
  let Y : ℝ := -S.sine*c.1+S.cosine*c.2
  have hnorm : X^2+Y^2 = normSq c := by
    calc
      _ = (S.cosine^2+S.sine^2)*normSq c := by dsimp [X,Y,normSq]; ring
      _ = normSq c := by rw [S.unit]; ring
  have hver (j : Fin 4) :
      normSq (add c (rotate S (localVertex j))) =
      normSq c+1/2+(![-X-Y,-X+Y,X-Y,X+Y] : Fin 4 → ℝ) j := by
    rw [normSq_add,normSq_rotate,localVertex_normSq]
    fin_cases j <;> norm_num [localVertex,rotate,dot,X,Y] <;> ring
  have h0 := hdisk 0
  have h1 := hdisk 1
  have h2 := hdisk 2
  have h3 := hdisk 3
  rw [hver] at h0 h1 h2 h3
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    at h0 h1 h2 h3
  have hmax : normSq c+1/2+|X|+|Y| ≤ R^2 := by
    by_cases hx : 0 ≤ X <;> by_cases hy : 0 ≤ Y
    · simp only [abs_of_nonneg hx,abs_of_nonneg hy]; linarith
    · simp only [abs_of_nonneg hx,abs_of_neg (lt_of_not_ge hy)]; linarith
    · simp only [abs_of_neg (lt_of_not_ge hx),abs_of_nonneg hy]; linarith
    · simp only [abs_of_neg (lt_of_not_ge hx),abs_of_neg (lt_of_not_ge hy)]; linarith
  have hr0 := Real.sqrt_nonneg (normSq c)
  have hrsq := Real.sq_sqrt (normSq_nonneg c)
  have habs0 : 0 ≤ |X|+|Y| := add_nonneg (abs_nonneg X) (abs_nonneg Y)
  have habssq : normSq c ≤ (|X|+|Y|)^2 := by
    have hm := mul_nonneg (abs_nonneg X) (abs_nonneg Y)
    nlinarith [sq_abs X,sq_abs Y]
  have hrabs : Real.sqrt (normSq c) ≤ |X|+|Y| := by
    nlinarith
  apply center_bound_algebra hr0
  nlinarith

lemma halfWidth_hasDerivAt (t : ℝ) :
    HasDerivAt halfWidth ((-Real.sin t+Real.cos t)/2) t := by
  have hfun : halfWidth = fun z : ℝ => (1 + Real.cos z + Real.sin z)/2 := by
    funext z; rfl
  rw [hfun]
  convert (((hasDerivAt_const t (1:ℝ)).add (Real.hasDerivAt_cos t)).add
    (Real.hasDerivAt_sin t)).div_const 2 using 1
  ring

lemma halfWidth_deriv_hasDerivAt (t : ℝ) :
    HasDerivAt (fun z : ℝ => (-Real.sin z+Real.cos z)/2)
      ((-Real.cos t-Real.sin t)/2) t := by
  convert ((Real.hasDerivAt_sin t).neg.add (Real.hasDerivAt_cos t)).div_const 2
    using 1

lemma halfWidth_concave : ConcaveOn ℝ (Set.Icc (0:ℝ) (Real.pi/3)) halfWidth := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := fun t => (-Real.sin t+Real.cos t)/2)
    (f'' := fun t => (-Real.cos t-Real.sin t)/2)
  · unfold halfWidth; fun_prop
  · intro t _; exact (halfWidth_hasDerivAt t).hasDerivWithinAt
  · intro t _; exact (halfWidth_deriv_hasDerivAt t).hasDerivWithinAt
  · intro t ht
    have hr := interior_subset ht
    have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi
      hr.1 (by linarith [hr.2,Real.pi_pos])
    have hc : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hr.1,Real.pi_pos], by linarith [hr.2,Real.pi_pos]⟩
    linarith

/-- A rational chord minorant valid throughout the whole interval. -/
lemma halfWidth_chord {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi/3) :
    1+(7/44:ℝ)*t ≤ halfWidth t := by
  let v : ℝ := t/(Real.pi/3)
  have hU : 0 < Real.pi/3 := by positivity
  have hv0 : 0 ≤ v := div_nonneg ht0 hU.le
  have hv1 : v ≤ 1 := (div_le_one hU).2 ht1
  have hvU : v*(Real.pi/3) = t := div_mul_cancel₀ t (ne_of_gt hU)
  have hj := halfWidth_concave.2
    (show (0:ℝ) ∈ Set.Icc 0 (Real.pi/3) by exact ⟨le_rfl,hU.le⟩)
    (show Real.pi/3 ∈ Set.Icc 0 (Real.pi/3) by exact ⟨hU.le,le_rfl⟩)
    (show 0 ≤ 1-v by linarith) hv0 (show 1-v+v=1 by ring)
  have hzero : halfWidth 0 = 1 := by norm_num [halfWidth]
  have hend : halfWidth (Real.pi/3) = (3+Real.sqrt 3)/4 := by
    rw [halfWidth,Real.cos_pi_div_three,Real.sin_pi_div_three]
    ring
  simp only [smul_eq_mul,mul_zero,zero_add,hvU,hzero,hend,mul_one] at hj
  have hsqrt : (5/3:ℝ) ≤ Real.sqrt 3 := by
    have hh := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg (3:ℝ)
    nlinarith
  have hm := mul_nonneg hv0 (sub_nonneg.mpr hsqrt)
  have hch : 1+v/6 ≤ halfWidth t := by nlinarith
  have hpi : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  have hu : Real.pi/3 ≤ 22/21 := by linarith
  have ht := mul_le_mul_of_nonneg_left hu hv0
  rw [hvU] at ht
  nlinarith

lemma dot_cauchy (p q : Point) :
    dot p q ≤ Real.sqrt (normSq p)*Real.sqrt (normSq q) := by
  have hdet : (dot p q)^2 ≤ normSq p*normSq q := by
    have hh := sq_nonneg (p.1*q.2-p.2*q.1)
    dsimp [dot,normSq]
    nlinarith
  have hp := Real.sq_sqrt (normSq_nonneg p)
  have hq := Real.sq_sqrt (normSq_nonneg q)
  have hprod : (Real.sqrt (normSq p)*Real.sqrt (normSq q))^2 = normSq p*normSq q := by
    rw [mul_pow,hp,hq]
  have hnn : 0 ≤ Real.sqrt (normSq p)*Real.sqrt (normSq q) := by positivity
  by_contra hn
  have hlt : Real.sqrt (normSq p)*Real.sqrt (normSq q) < dot p q := lt_of_not_ge hn
  have hh := mul_pos (sub_pos.mpr hlt)
    (show 0 < dot p q+Real.sqrt (normSq p)*Real.sqrt (normSq q) by linarith)
  nlinarith

lemma cardinal_normSq (t : ℝ) (k : Fin 4) :
    normSq (rotation t (castPoint (dirs k))) = 1 := by
  rw [rotation_normSq]
  fin_cases k <;> norm_num [normSq,castPoint,dirs]

lemma same_cardinal_chord (a b : ℝ) (k : Fin 4) :
    Real.sqrt (normSq (sub (rotation a (castPoint (dirs k)))
      (rotation b (castPoint (dirs k))))) ≤ |a-b| := by
  have he : normSq (sub (rotation a (castPoint (dirs k)))
      (rotation b (castPoint (dirs k)))) = 2-2*Real.cos (a-b) := by
    rw [Real.cos_sub]
    fin_cases k <;> norm_num [normSq,sub,rotation,castPoint,dirs] <;>
      nlinarith [Real.sin_sq_add_cos_sq a,Real.sin_sq_add_cos_sq b]
  have hs := Real.sq_sqrt (normSq_nonneg
    (sub (rotation a (castPoint (dirs k))) (rotation b (castPoint (dirs k)))))
  have hn := Real.sqrt_nonneg (normSq
    (sub (rotation a (castPoint (dirs k))) (rotation b (castPoint (dirs k)))))
  have hcos := Real.one_sub_sq_div_two_le_cos (x := a-b)
  rw [he] at hs
  -- (a-b)^2 >= 2 - 2cos(a-b) = the squared norm, and both sides are nonneg.
  have hsq : Real.sqrt (normSq
      (sub (rotation a (castPoint (dirs k))) (rotation b (castPoint (dirs k))))) ^ 2
      ≤ |a-b| ^ 2 := by
    rw [Real.sq_sqrt (normSq_nonneg _), he, sq_abs]
    linarith
  nlinarith [hsq, hn, abs_nonneg (a-b)]

lemma common_cardinal_chain_bound (c₀ c₁ c₂ : Point) (a b : ℝ) (k : Fin 4)
    (h₀ : Real.sqrt (normSq c₀) ≤ 11/16)
    (h₁ : Real.sqrt (normSq c₁) ≤ 11/16)
    (h₂ : Real.sqrt (normSq c₂) ≤ 11/16)
    {u v : ℝ}
    (hu : u ≤ dot (rotation a (castPoint (dirs k))) (sub c₁ c₀))
    (hv : v ≤ dot (rotation b (castPoint (dirs k))) (sub c₂ c₁)) :
    u+v ≤ 11/8+(11/16)*|a-b| := by
  let n₁ := rotation a (castPoint (dirs k))
  let n₂ := rotation b (castPoint (dirs k))
  have hneg : normSq (scale (-1) n₁) = 1 := by
    have he : normSq (scale (-1) n₁) = normSq n₁ := by dsimp [normSq,scale]; ring
    rw [he]
    exact cardinal_normSq a k
  have hleft := dot_cauchy (scale (-1) n₁) c₀
  rw [hneg,Real.sqrt_one,one_mul] at hleft
  have hright := dot_cauchy n₂ c₂
  rw [cardinal_normSq b k,Real.sqrt_one,one_mul] at hright
  have hmid := dot_cauchy (sub n₁ n₂) c₁
  have hmid' : Real.sqrt (normSq (sub n₁ n₂))*Real.sqrt (normSq c₁) ≤
      |a-b| * (11/16) :=
    mul_le_mul (same_cardinal_chord a b k) h₁ (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsum : dot n₁ (sub c₁ c₀)+dot n₂ (sub c₂ c₁) =
      dot (scale (-1) n₁) c₀+dot (sub n₁ n₂) c₁+dot n₂ c₂ := by
    dsimp [dot,sub,scale]; ring
  change u ≤ dot n₁ (sub c₁ c₀) at hu
  change v ≤ dot n₂ (sub c₂ c₁) at hv
  linarith

def pairEdge (i j : Fin 3) : Fin 3 :=
  if (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) then 0
  else if (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) then 1 else 2

lemma pairEdge_symmetric : ∀ i j : Fin 3, pairEdge j i = pairEdge i j := by decide

lemma direction_reverse : ∀ (k₁ k₂ : Fin 4) (i j : Fin 3), i ≠ j →
    Combinatorics.direction k₁ k₂ j i = Combinatorics.direction k₁ k₂ i j+2 := by
  decide

def directedNormal (x : Point) (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3)
    (i j : Fin 3) : Point :=
  rotation (theta x (s (pairEdge i j)))
    (castPoint (dirs (Combinatorics.direction (k 1) (k 2) i j)))

lemma directedNormal_reverse (x : Point) (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3)
    (i j : Fin 3) (hij : i ≠ j) :
    directedNormal x k s j i = scale (-1) (directedNormal x k s i j) := by
  unfold directedNormal
  rw [pairEdge_symmetric i j,direction_reverse (k 1) (k 2) i j hij,
    opposite_cardinal,rotation_scale]

lemma theta_bounds {x : Point} (hx : AngleDomain.Domain x.1 x.2) (i : Fin 3) :
    0 ≤ theta x i ∧ theta x i ≤ Real.pi*x.2 := by
  have ha := (argument_ranges hx 0).1
  have hb := (argument_ranges hx 1).1
  have hd := (argument_ranges hx 2).1
  simp only [arguments] at ha hb hd
  norm_num at ha hb hd
  fin_cases i <;> simp only [theta] <;> norm_num <;>
    first
      | linarith
      | (constructor <;> linarith)

lemma theta_spread {x : Point} (hx : AngleDomain.Domain x.1 x.2) (i j : Fin 3) :
    |theta x i-theta x j| ≤ Real.pi*x.2 := by
  have hi := theta_bounds hx i
  have hj := theta_bounds hx j
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma pair_angle_range {x : Point} (hx : AngleDomain.Domain x.1 x.2) (i j : Fin 3) :
    0 ≤ |theta x j-theta x i| ∧ |theta x j-theta x i| ≤ Real.pi/3 := by
  have hb := (argument_ranges hx 1).2
  have hs := theta_spread hx j i
  simp only [arguments] at hb
  norm_num at hb
  exact ⟨abs_nonneg _,by linarith⟩

lemma path_spread {x : Point} (hx : AngleDomain.Domain x.1 x.2)
    (i j l : Fin 3) (hij : i ≠ j) (hjl : j ≠ l) (hil : i ≠ l) :
    Real.pi*x.2 ≤ |theta x j-theta x i|+|theta x l-theta x j| := by
  have ha : 0 ≤ Real.pi*x.1 := by
    have := (argument_ranges hx 0).1
    simp only [arguments] at this
    norm_num at this
    linarith
  have hb : 0 ≤ Real.pi*x.2 := by
    have := (argument_ranges hx 1).1
    simp only [arguments] at this
    norm_num at this
    linarith
  have hd : 0 ≤ Real.pi*x.2-Real.pi*x.1 := by
    have := (argument_ranges hx 2).1
    simp only [arguments] at this
    norm_num at this
    linarith
  have hrev : |Real.pi*x.1-Real.pi*x.2| = Real.pi*x.2-Real.pi*x.1 := by
    rw [abs_sub_comm,abs_of_nonneg hd]
  have hx1 : 0 ≤ x.1 := hx.1
  have hx1abs : |x.1| = x.1 := abs_of_nonneg hx1
  have hx2 : 0 ≤ x.2 := by nlinarith [Real.pi_pos]
  have hx2abs : |x.2| = x.2 := abs_of_nonneg hx2
  fin_cases i <;> fin_cases j <;> fin_cases l
  all_goals
    first
      | (exfalso; revert hij hjl hil; decide)
      | (simp only [theta]
         norm_num
         simp only [abs_of_nonneg hd,hrev,hx1abs,hx2abs]
         try linarith)

lemma directed_separation {c : Fin 3 → Point} {x : Point}
    (hx : AngleDomain.Domain x.1 x.2) (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3)
    (hk0 : k 0=0)
    (hsep : ∀ e, widths x e ≤ dot (normal x k s e)
      (sub (c (edgeEnd e)) (c (edgeStart e))))
    (i j : Fin 3) (hij : i ≠ j) :
    halfWidth |theta x j-theta x i| ≤ dot (directedNormal x k s i j) (sub (c j) (c i)) := by
  have ha : 0 ≤ Real.pi*x.1 := by
    have := (argument_ranges hx 0).1
    simp only [arguments] at this
    norm_num at this
    linarith
  have hb : 0 ≤ Real.pi*x.2 := by
    have := (argument_ranges hx 1).1
    simp only [arguments] at this
    norm_num at this
    linarith
  have hd : 0 ≤ Real.pi*x.2-Real.pi*x.1 := by
    have := (argument_ranges hx 2).1
    simp only [arguments] at this
    norm_num at this
    linarith
  have hf (i j : Fin 3) (hij : i < j) :
      halfWidth |theta x j-theta x i| ≤ dot (directedNormal x k s i j) (sub (c j) (c i)) := by
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · simpa [directedNormal,pairEdge,Combinatorics.direction,normal,widths,
        arguments,theta,edgeStart,edgeEnd,hk0,abs_of_nonneg ha] using hsep 0
    · simpa [directedNormal,pairEdge,Combinatorics.direction,normal,widths,
        arguments,theta,edgeStart,edgeEnd,abs_of_nonneg hb] using hsep 1
    · simpa [directedNormal,pairEdge,Combinatorics.direction,normal,widths,
        arguments,theta,edgeStart,edgeEnd,abs_of_nonneg hd] using hsep 2
  by_cases hlt : i < j
  · exact hf i j hlt
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hlt) hij.symm
    have hh := hf j i hji
    have he : dot (directedNormal x k s i j) (sub (c j) (c i)) =
        dot (directedNormal x k s j i) (sub (c i) (c j)) := by
      rw [directedNormal_reverse x k s j i hij.symm]
      dsimp [dot,sub,scale]
      ring
    rw [he,abs_sub_comm]
    exact hh

/-- Two separation inequalities cannot form a directed chain with the same
cardinal index: their lower and upper support estimates are incompatible. -/
theorem forbidden_chain (c : Fin 3 → Point) (x : Point) (R : ℝ)
    (hx : AngleDomain.Domain x.1 x.2)
    (hp : Packing (angularSquares c x) (0,0) R)
    (hsmall : R^2 < targetSq)
    (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3)
    (hk0 : k 0 = 0)
    (_hs : ∀ e, s e = first e ∨ s e = last e)
    (hsep : ∀ e, widths x e ≤ dot (normal x k s e)
      (sub (c (edgeEnd e)) (c (edgeStart e)))) :
    ¬ Combinatorics.hasChain (k 1) (k 2) := by
  have hc (i : Fin 3) : Real.sqrt (normSq (c i)) ≤ 11/16 := by
    apply square_center_bound (angularSquares c x i) (c i) R
    · intro j
      simpa [angularSquares,sub,add] using packing_vertex_bound hp i j
    · exact hsmall.le
  rintro ⟨i,j,l,hij,hjl,hil,hdir⟩
  let a := theta x (s (pairEdge i j))
  let b := theta x (s (pairEdge j l))
  let q := Combinatorics.direction (k 1) (k 2) i j
  let δ₁ := |theta x j-theta x i|
  let δ₂ := |theta x l-theta x j|
  have h₁ := directed_separation hx k s hk0 hsep i j hij
  have h₂ := directed_separation hx k s hk0 hsep j l hjl
  have hlo₁ := halfWidth_chord (pair_angle_range hx i j).1 (pair_angle_range hx i j).2
  have hlo₂ := halfWidth_chord (pair_angle_range hx j l).1 (pair_angle_range hx j l).2
  have hupper : halfWidth δ₁+halfWidth δ₂ ≤ 11/8+(11/16)*|a-b| := by
    apply common_cardinal_chain_bound (c i) (c j) (c l) a b q (hc i) (hc j) (hc l)
    · exact h₁
    · simpa only [directedNormal,a,b,q,hdir] using h₂
  have hφ : |a-b| ≤ Real.pi*x.2 := theta_spread hx _ _
  have hpath : Real.pi*x.2 ≤ δ₁+δ₂ := path_spread hx i j l hij hjl hil
  have hlower : 2+(7/44:ℝ)*|a-b| ≤ halfWidth δ₁+halfWidth δ₂ := by
    change 1+(7/44:ℝ)*δ₁ ≤ halfWidth δ₁ at hlo₁
    change 1+(7/44:ℝ)*δ₂ ≤ halfWidth δ₂ at hlo₂
    linarith
  have hb := (argument_ranges hx 1).2
  have hφbound : |a-b| ≤ 22/21 := by
    simp only [arguments] at hb
    norm_num at hb
    linarith [Real.pi_lt_d4]
  exact chain_contradiction hφbound hlower hupper

end ThreeUnitSquaresInCircle.Cert
