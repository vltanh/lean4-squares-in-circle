import ThreeUnitSquaresInCircle.OrientationNormalization

/-!
Separating axes for two squares, derived from open-set separation and an
explicit eight-sector support calculation. This does not assume a polygon SAT.
Compiles against Lean 4.34.0 / mathlib v4.34.0.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Cert
open RatData

lemma weighted_strict {a b u v H : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a+b) (hu : u < H) (hv : v < H) :
    a*u+b*v < H*(a+b) := by
  have h₁ := mul_nonneg ha (sub_nonneg.mpr hu.le)
  have h₂ := mul_nonneg hb (sub_nonneg.mpr hv.le)
  by_cases hapos : 0 < a
  · have h := mul_pos hapos (sub_pos.mpr hu)
    nlinarith
  · have hbpos : 0 < b := by linarith
    have h := mul_pos hbpos (sub_pos.mpr hv)
    nlinarith

lemma abs_affine_lt {a b u v r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hu : |u| < r) (hv : |v| < r) : |a*u+b*v| < r := by
  rcases abs_lt.mp hu with ⟨hu0,hu1⟩
  rcases abs_lt.mp hv with ⟨hv0,hv1⟩
  have h₁ := weighted_strict ha hb (by linarith : 0 < a+b) hu1 hv1
  have h₂ := weighted_strict ha hb (by linarith : 0 < a+b)
    (show -u < r by linarith) (show -v < r by linarith)
  rw [hab] at h₁ h₂
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

lemma openSquare_convex (S : UnitSquare) : Convex ℝ {p | openSquare S p} := by
  intro p hp q hq a b ha hb hab
  have hx : localX S (a • p+b • q) = a*localX S p+b*localX S q := by
    calc
      _ = a*localX S p+b*localX S q+
          (a+b-1)*(S.cosine*S.center.1+S.sine*S.center.2) := by
        dsimp [localX]; ring
      _ = _ := by rw [hab]; ring
  have hy : localY S (a • p+b • q) = a*localY S p+b*localY S q := by
    calc
      _ = a*localY S p+b*localY S q+
          (a+b-1)*(-S.sine*S.center.1+S.cosine*S.center.2) := by
        dsimp [localY]; ring
      _ = _ := by rw [hab]; ring
  exact ⟨by rw [hx]; exact abs_affine_lt ha hb hab hp.1 hq.1,
    by rw [hy]; exact abs_affine_lt ha hb hab hp.2 hq.2⟩

lemma openSquare_isOpen (S : UnitSquare) : IsOpen {p | openSquare S p} := by
  have hX : Continuous (localX S) := by unfold localX; fun_prop
  have hY : Continuous (localY S) := by unfold localY; fun_prop
  exact (isOpen_lt hX.abs continuous_const).inter
    (isOpen_lt hY.abs continuous_const)

lemma center_in_openSquare (S : UnitSquare) : openSquare S S.center := by
  norm_num [openSquare,localX,localY]

def supportRadius (S : UnitSquare) (n : Point) : ℝ :=
  (|S.cosine*n.1+S.sine*n.2|+|-S.sine*n.1+S.cosine*n.2|)/2

lemma supportRadius_nonneg (S : UnitSquare) (n : Point) : 0 ≤ supportRadius S n := by
  unfold supportRadius; positivity

lemma supportRadius_neg (S : UnitSquare) (n : Point) :
    supportRadius S (scale (-1) n) = supportRadius S n := by
  have h₁ : S.cosine*(-n.1)+S.sine*(-n.2) = -(S.cosine*n.1+S.sine*n.2) := by ring
  have h₂ : -S.sine*(-n.1)+S.cosine*(-n.2) = -(-S.sine*n.1+S.cosine*n.2) := by ring
  simp only [supportRadius,scale,neg_one_mul,h₁,h₂,abs_neg]

lemma signed_half_product (X t : ℝ) :
    X*(if 0 ≤ X then t/2 else -t/2) = t*|X|/2 := by
  split_ifs with hX
  · rw [abs_of_nonneg hX]; ring
  · rw [abs_of_neg (lt_of_not_ge hX)]; ring

/-- Shrunk support vertices lie in the open square, even when a coefficient is zero. -/
lemma support_point (S : UnitSquare) (n : Point) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ p : Point, openSquare S p ∧
      dot n p = dot n S.center+t*supportRadius S n := by
  let X := S.cosine*n.1+S.sine*n.2
  let Y := -S.sine*n.1+S.cosine*n.2
  let q : Point := (if 0 ≤ X then t/2 else -t/2,
                    if 0 ≤ Y then t/2 else -t/2)
  refine ⟨add S.center (rotate S q), ?_, ?_⟩
  · rw [openSquare,localX_rotated,localY_rotated]
    have ht : |t/2| = t/2 := abs_of_nonneg (by positivity)
    dsimp [q]
    have htn : |(-(t/2))| = t/2 := by rw [abs_neg]; exact ht
    have hneg : -t/2 = -(t/2) := by ring
    constructor <;> split_ifs <;>
      simp only [hneg, ht, htn] <;> linarith
  · calc
      dot n (add S.center (rotate S q)) =
          dot n S.center+X*q.1+Y*q.2 := by
        dsimp [dot,add,rotate,X,Y]; ring
      _ = dot n S.center+t*|X|/2+t*|Y|/2 := by
        dsimp [q]
        rw [signed_half_product,signed_half_product]
      _ = dot n S.center+t*supportRadius S n := by
        dsimp [supportRadius,X,Y]; ring

lemma bound_from_shrinks {H D : ℝ} (_hH : 0 ≤ H)
    (h : ∀ t : ℝ, 0 ≤ t → t < 1 → t*H ≤ D) : H ≤ D := by
  have hD : 0 ≤ D := by simpa using h 0 (by norm_num) (by norm_num)
  by_contra hn
  have hDH : D < H := lt_of_not_ge hn
  have hHp : 0 < H := by linarith
  let t : ℝ := (D/H+1)/2
  have hd0 : 0 ≤ D/H := div_nonneg hD hHp.le
  have hd1 : D/H < 1 := (div_lt_one hHp).2 hDH
  have ht0 : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have htH : t*H = (D+H)/2 := by
    dsimp [t]
    field_simp
  have hh := h t ht0 ht1
  rw [htH] at hh
  linarith

/-- A nonzero supporting functional for two squares with disjoint open interiors. -/
lemma support_separator (S T : UnitSquare)
    (hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    ∃ n : Point, n ≠ (0,0) ∧
      supportRadius S n+supportRadius T n ≤ dot n (sub T.center S.center) := by
  have hd : Disjoint {p | openSquare S p} {p | openSquare T p} := by
    rw [Set.disjoint_left]
    exact fun p hp hq => hdisj p ⟨hp,hq⟩
  obtain ⟨f,u,hS,hT⟩ := geometric_hahn_banach_open_open
    (openSquare_convex S) (openSquare_isOpen S)
    (openSquare_convex T) (openSquare_isOpen T) hd
  let n : Point := (f (1,0), f (0,1))
  have hf (p : Point) : f p = dot n p := by
    have he : p = p.1 • (1,0) + p.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
    dsimp [dot,n]
    ring
  have hn : n ≠ (0,0) := by
    intro hn
    have hh := lt_trans (hS _ (center_in_openSquare S))
      (hT _ (center_in_openSquare T))
    rw [hf,hf,hn] at hh
    norm_num [dot] at hh
  refine ⟨n,hn,bound_from_shrinks
    (add_nonneg (supportRadius_nonneg S n) (supportRadius_nonneg T n)) ?_⟩
  intro t ht0 ht1
  obtain ⟨p,hp,hpval⟩ := support_point S n ht0 ht1
  obtain ⟨q,hq,hqval⟩ := support_point T (scale (-1) n) ht0 ht1
  have hsep := lt_trans (hS p hp) (hT q hq)
  rw [hf,hf,hpval] at hsep
  rw [supportRadius_neg] at hqval
  simp only [dot,scale,neg_one_mul] at hqval
  dsimp [dot,sub] at hsep ⊢
  nlinarith

def axisInside (c s : ℝ) (d : Point) : Prop :=
  let H := (1+c+s)/2
  |d.1| < H ∧ |d.2| < H ∧ |c*d.1+s*d.2| < H ∧ |-s*d.1+c*d.2| < H

def octagonSupport (c s : ℝ) (n : Point) : ℝ :=
  (|n.1|+|n.2|+|c*n.1+s*n.2|+|-s*n.1+c*n.2|)/2

/-- In the first quadrant there are just two sectors, split by the rotated x axis. -/
lemma octagon_first_quadrant {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (d n : Point) (hd : axisInside c s d)
    (hx : 0 ≤ n.1) (hy : 0 ≤ n.2) (hn : 0 < n.1+n.2) :
    dot n d < octagonSupport c s n := by
  have hxD := (abs_lt.mp hd.1).2
  have hyD := (abs_lt.mp hd.2.1).2
  have hpD := (abs_lt.mp hd.2.2.1).2
  have hp : 0 ≤ c*n.1+s*n.2 := by positivity
  by_cases hs0 : s=0
  · have hc1 : c=1 := by nlinarith
    subst s; subst c
    have hh := weighted_strict hx hy hn hxD hyD
    simp only [dot, octagonSupport, one_mul, zero_mul, neg_zero, add_zero, zero_add,
      abs_of_nonneg hx, abs_of_nonneg hy]
    linarith [hh]
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hw : -s*n.1+c*n.2 ≤ 0
    · let a := s*n.1-c*n.2
      have ha : 0 ≤ a := by dsimp [a]; linarith
      have hab : 0 < a+n.2 := by
        by_contra hh
        have hny : n.2=0 := by linarith
        have hnx : 0 < n.1 := by linarith
        have hh' := mul_pos hsp hnx
        dsimp [a] at *
        nlinarith
      have hlt := weighted_strict ha hy hab hxD hpD
      have he₁ : a*d.1+n.2*(c*d.1+s*d.2) = s*dot n d := by
        dsimp [a,dot]; ring
      have he₂ : ((1+c+s)/2)*(a+n.2) = s*octagonSupport c s n := by
        simp only [octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,
          abs_of_nonneg hp,abs_of_nonpos hw]
        dsimp [a]
        linear_combination -(n.2/2)*hunit
      rw [he₁,he₂] at hlt
      exact lt_of_mul_lt_mul_left (by linarith [hlt]) hsp.le
    · have hw0 : 0 ≤ -s*n.1+c*n.2 := le_of_lt (lt_of_not_ge hw)
      let b := c*n.2-s*n.1
      have hb : 0 ≤ b := by dsimp [b]; linarith
      have hab : 0 < n.1+b := by
        by_contra hh
        have hnx : n.1=0 := by linarith
        have hny : 0 < n.2 := by linarith
        have hh' := mul_pos hc hny
        dsimp [b] at *
        nlinarith
      have hlt := weighted_strict hx hb hab hpD hyD
      have he₁ : n.1*(c*d.1+s*d.2)+b*d.2 = c*dot n d := by
        dsimp [b,dot]; ring
      have he₂ : ((1+c+s)/2)*(n.1+b) = c*octagonSupport c s n := by
        simp only [octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,
          abs_of_nonneg hp,abs_of_nonneg hw0]
        dsimp [b]
        linear_combination -(n.1/2)*hunit
      rw [he₁,he₂] at hlt
      exact lt_of_mul_lt_mul_left (by linarith [hlt]) hc.le

def qturn (p : Point) : Point := (-p.2,p.1)
def qturns : ℕ → Point → Point
  | 0,p => p
  | n+1,p => qturn (qturns n p)

lemma qturn_axisInside {c s : ℝ} {d : Point} (hd : axisInside c s d) :
    axisInside c s (qturn d) := by
  have h₁ : c*(-d.2)+s*d.1 = -(-s*d.1+c*d.2) := by ring
  have h₂ : -s*(-d.2)+c*d.1 = c*d.1+s*d.2 := by ring
  simpa only [axisInside,qturn,abs_neg,h₁,h₂] using
    And.intro hd.2.1 (And.intro hd.1 (And.intro hd.2.2.2 hd.2.2.1))

lemma qturn_support (c s : ℝ) (n : Point) :
    octagonSupport c s (qturn n) = octagonSupport c s n := by
  have h₁ : c*(-n.2)+s*n.1 = -(-s*n.1+c*n.2) := by ring
  have h₂ : -s*(-n.2)+c*n.1 = c*n.1+s*n.2 := by ring
  simp only [octagonSupport,qturn,h₁,h₂,abs_neg]
  ring

lemma qturns_facts (k : ℕ) (c s : ℝ) (n d : Point) :
    (axisInside c s d → axisInside c s (qturns k d)) ∧
    octagonSupport c s (qturns k n) = octagonSupport c s n ∧
    dot (qturns k n) (qturns k d) = dot n d ∧
    normSq (qturns k n) = normSq n := by
  induction k with
  | zero => exact ⟨id,rfl,rfl,rfl⟩
  | succ k ih =>
    refine ⟨fun h => qturn_axisInside (ih.1 h), ?_, ?_, ?_⟩
    · rw [qturns,qturn_support,ih.2.1]
    · calc
        _ = dot (qturns k n) (qturns k d) := by dsimp [qturns,qturn,dot]; ring
        _ = dot n d := ih.2.2.1
    · calc
        _ = normSq (qturns k n) := by dsimp [qturns,qturn,normSq]; ring
        _ = normSq n := ih.2.2.2

lemma qturn_first_quadrant (n : Point) :
    ∃ k : Fin 4, 0 ≤ (qturns k.val n).1 ∧ 0 ≤ (qturns k.val n).2 := by
  by_cases hx : 0 ≤ n.1 <;> by_cases hy : 0 ≤ n.2
  · exact ⟨0,hx,hy⟩
  · refine ⟨1,?_,?_⟩ <;> dsimp [qturns,qturn] <;> linarith
  · refine ⟨3,?_,?_⟩ <;> dsimp [qturns,qturn] <;> linarith
  · refine ⟨2,?_,?_⟩ <;> dsimp [qturns,qturn] <;> linarith

lemma octagon_strict {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) {d n : Point} (hd : axisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  obtain ⟨k,hx,hy⟩ := qturn_first_quadrant n
  have hf := qturns_facts k.val c s n d
  have hpos : 0 < (qturns k.val n).1+(qturns k.val n).2 := by
    by_contra hh
    have hx0 : (qturns k.val n).1=0 := by linarith
    have hy0 : (qturns k.val n).2=0 := by linarith
    have hn0 : normSq n=0 := by
      rw [← hf.2.2.2]
      simp [normSq,hx0,hy0]
    apply hn
    apply Prod.ext <;> dsimp [normSq] at hn0 ⊢ <;>
      nlinarith [sq_nonneg n.1,sq_nonneg n.2]
  have hh := octagon_first_quadrant hc hs hunit (qturns k.val d)
    (qturns k.val n) (hf.1 hd) hx hy hpos
  simpa only [hf.2.1,hf.2.2.1] using hh

/-- The four unsigned edge axes are exhaustive; strict overlap on all four
would contradict the supporting functional. -/
lemma axis_separation_zero (d : Point) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ Real.pi/3)
    (hdisj : ∀ p, ¬ (openSquare (aframe (0,0) 0) p ∧ openSquare (aframe d δ) p)) :
    halfWidth δ ≤ |d.1| ∨ halfWidth δ ≤ |d.2| ∨
    halfWidth δ ≤ |Real.cos δ*d.1+Real.sin δ*d.2| ∨
    halfWidth δ ≤ |-Real.sin δ*d.1+Real.cos δ*d.2| := by
  obtain ⟨n,hn,hsep⟩ := support_separator (aframe (0,0) 0) (aframe d δ) hdisj
  have hc : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi
    hδ0 (by linarith [Real.pi_pos])
  by_contra hh
  push Not at hh
  have hi : axisInside (Real.cos δ) (Real.sin δ) d := by
    simpa only [axisInside,halfWidth] using hh
  have hlt := octagon_strict hc hs (by nlinarith [Real.sin_sq_add_cos_sq δ]) hi hn
  have he : supportRadius (aframe (0,0) 0) n+supportRadius (aframe d δ) n =
      octagonSupport (Real.cos δ) (Real.sin δ) n := by
    simp only [supportRadius,aframe,Real.cos_zero,Real.sin_zero,
      one_mul,zero_mul,neg_zero,zero_add,add_zero,octagonSupport]
    ring
  rw [he] at hsep
  simp only [aframe,sub,sub_zero] at hsep
  exact not_lt_of_ge hsep hlt

end ThreeUnitSquaresInCircle.Cert
