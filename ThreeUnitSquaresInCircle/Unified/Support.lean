import ThreeUnitSquaresInCircle.Unified.Tangents
import ThreeUnitSquaresInCircle.SeparatingAxes

/-!
# The common octagon support estimate and safe radial extension

The support estimate does not require a bound on the angle between squares.
The final `safe_openRay_of_disjoint` theorem uses an arbitrary nonzero separating
functional from the repository's proved `support_separator`.  No separating-axis
enumeration or additional geometric hypothesis is required.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

/-- Support function of the local octagon, evaluated on nonnegative coordinates. -/
def octSupport (p q : ℝ) : ℝ := max p (max q (3*(p+q)/4))

lemma octagon_linear_le {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (h : P8 a b) :
    p*a+q*b ≤ octSupport p q := by
  rcases h with ⟨h₀,h₁⟩
  by_cases hdom : 3*q ≤ p
  · have hmul := mul_le_mul_of_nonneg_left h₀ (show 0 ≤ p/3 by positivity)
    have hrem := mul_nonneg (show 0 ≤ p/3-q by linarith) hb
    exact le_trans (by nlinarith : p*a+q*b ≤ p) (le_max_left _ _)
  · by_cases hdom' : 3*p ≤ q
    · have hmul := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ q/3 by positivity)
      have hrem := mul_nonneg (show 0 ≤ q/3-p by linarith) ha
      exact le_trans (by nlinarith : p*a+q*b ≤ q)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · have hA : 0 ≤ (3*p-q)/8 := by linarith
      have hB : 0 ≤ (3*q-p)/8 := by linarith
      have hmul₀ := mul_le_mul_of_nonneg_left h₀ hA
      have hmul₁ := mul_le_mul_of_nonneg_left h₁ hB
      exact le_trans (by nlinarith : p*a+q*b ≤ 3*(p+q)/4)
        (le_trans (le_max_right _ _) (le_max_right _ _))

lemma octagon_linear_lt {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hp : 0 ≤ p) (_hq : 0 ≤ q) (hpq : 0 < p+q) (h : P8Strict a b) :
    p*a+q*b < octSupport p q := by
  rcases h with ⟨h₀,h₁⟩
  by_cases hdom : 3*q ≤ p
  · have hpp : 0 < p := by linarith
    have hmul := mul_lt_mul_of_pos_left h₀ (show 0 < p/3 by positivity)
    have hrem := mul_nonneg (show 0 ≤ p/3-q by linarith) hb
    exact lt_of_lt_of_le (by nlinarith : p*a+q*b < p) (le_max_left _ _)
  · by_cases hdom' : 3*p ≤ q
    · have hqq : 0 < q := by linarith
      have hmul := mul_lt_mul_of_pos_left h₁ (show 0 < q/3 by positivity)
      have hrem := mul_nonneg (show 0 ≤ q/3-p by linarith) ha
      exact lt_of_lt_of_le (by nlinarith : p*a+q*b < q)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · have hA : 0 ≤ (3*p-q)/8 := by linarith
      have hB : 0 ≤ (3*q-p)/8 := by linarith
      have hw := Cert.weighted_strict hA hB
        (show 0 < (3*p-q)/8+(3*q-p)/8 by linarith) h₀ h₁
      exact lt_of_lt_of_le (by nlinarith : p*a+q*b < 3*(p+q)/4)
        (le_trans (le_max_right _ _) (le_max_right _ _))

def width (S : UnitSquare) (n : Point) : ℝ :=
  (|frameX S n|+|frameY S n|)/2

lemma dot_center_abs_le (S : UnitSquare) (o n : Point) :
    |dot n (sub S.center o)| ≤
      |frameX S n| * alpha S o + |frameY S n| * beta S o := by
  rw [← frame_dot S]
  calc
    _ ≤ |frameX S n * frameX S (sub S.center o)| +
        |frameY S n * frameY S (sub S.center o)| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_mul,abs_frame_centerX,abs_frame_centerY]

lemma dot_center_le (S : UnitSquare) (o n : Point)
    (h : P8 (alpha S o) (beta S o)) :
    |dot n (sub S.center o)| ≤ octSupport |frameX S n| |frameY S n| :=
  (dot_center_abs_le S o n).trans
    (octagon_linear_le (alpha_nonneg _ _) (beta_nonneg _ _)
      (abs_nonneg _) (abs_nonneg _) h)

/-- Union of translates of the *open* square along the ray away from `o`. -/
def openRay (S : UnitSquare) (o : Point) : Set Point :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ ∃ q, openSquare S q ∧
    p = add q (scale t (sub S.center o))}

lemma openSquare_subset_openRay (S : UnitSquare) (o : Point) :
    {p | openSquare S p} ⊆ openRay S o := by
  intro p hp
  exact ⟨0,le_rfl,p,hp,by simp [add,scale]⟩

/-! ## General separators: no edge-axis reduction is needed for extension. -/

lemma frame_abs_sum_pos (S : UnitSquare) {n : Point} (hn : n ≠ (0,0)) :
    0 < |frameX S n|+|frameY S n| := by
  have hh := frame_norm S n
  by_contra hnot
  have hx : frameX S n=0 := by
    have ha : |frameX S n|=0 := by nlinarith [abs_nonneg (frameX S n),abs_nonneg (frameY S n)]
    exact abs_eq_zero.mp ha
  have hy : frameY S n=0 := by
    have ha : |frameY S n|=0 := by nlinarith [abs_nonneg (frameX S n),abs_nonneg (frameY S n)]
    exact abs_eq_zero.mp ha
  rw [hx,hy] at hh
  apply hn
  apply Prod.ext <;> dsimp [normSq] at hh ⊢ <;>
    nlinarith [sq_nonneg n.1,sq_nonneg n.2]

/-- A support bound for *every* normal, not just a square edge normal. -/
lemma octSupport_le_widths (S T : UnitSquare) (n : Point) :
    octSupport |frameX S n| |frameY S n| ≤ width S n+width T n := by
  let p := |frameX S n|
  let q := |frameY S n|
  let u := |frameX T n|
  let v := |frameY T n|
  have hp : 0 ≤ p := abs_nonneg _
  have hq : 0 ≤ q := abs_nonneg _
  have hu : 0 ≤ u := abs_nonneg _
  have hv : 0 ≤ v := abs_nonneg _
  have he : p^2+q^2=u^2+v^2 := by
    simp only [p,q,u,v,sq_abs,frame_norm]
  have hp' : p ≤ u+v := by
    nlinarith [sq_nonneg q,mul_nonneg hu hv]
  have hq' : q ≤ u+v := by
    nlinarith [sq_nonneg p,mul_nonneg hu hv]
  change max p (max q (3*(p+q)/4)) ≤ (p+q)/2+(u+v)/2
  exact max_le (by linarith) (max_le (by linarith) (by linarith))

structure Separation (S T : UnitSquare) where
  normal : Point
  nonzero : normal ≠ (0,0)
  separates : width S normal+width T normal ≤ dot normal (sub T.center S.center)

/-- Reuse the repository's proved Hahn--Banach separation theorem. -/
lemma separation_exists (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) : Nonempty (Separation S T) := by
  obtain ⟨n,hn,hsep⟩ := Cert.support_separator S T hd
  exact ⟨⟨n,hn,hsep⟩⟩

lemma dot_center_lt_of_ne (S : UnitSquare) (o : Point) {n : Point}
    (hn : n ≠ (0,0)) (h : P8Strict (alpha S o) (beta S o)) :
    |dot n (sub S.center o)| < octSupport |frameX S n| |frameY S n| :=
  lt_of_le_of_lt (dot_center_abs_le S o n)
    (octagon_linear_lt (alpha_nonneg _ _) (beta_nonneg _ _)
      (abs_nonneg _) (abs_nonneg _) (frame_abs_sum_pos S hn) h)

lemma Separation.center_signs {S T : UnitSquare} (e : Separation S T) (o : Point)
    (hS : P8 (alpha S o) (beta S o)) (hT : P8 (alpha T o) (beta T o)) :
    dot e.normal (sub S.center o) ≤ 0 ∧ 0 ≤ dot e.normal (sub T.center o) := by
  have h₁ := (dot_center_le S o e.normal hS).trans (octSupport_le_widths S T e.normal)
  have h₂ := (dot_center_le T o e.normal hT).trans (octSupport_le_widths T S e.normal)
  have hsep := e.separates
  rcases abs_le.mp h₁ with ⟨h₁a,h₁b⟩
  rcases abs_le.mp h₂ with ⟨h₂a,h₂b⟩
  simp only [dot_sub_right] at *
  exact ⟨by linarith,by linarith⟩

lemma Separation.strict_center_signs {S T : UnitSquare} (e : Separation S T) (o : Point)
    (hS : P8Strict (alpha S o) (beta S o)) (hT : P8Strict (alpha T o) (beta T o)) :
    dot e.normal (sub S.center o) < 0 ∧ 0 < dot e.normal (sub T.center o) := by
  have h₁ := (dot_center_lt_of_ne S o e.nonzero hS).trans_le (octSupport_le_widths S T e.normal)
  have h₂ := (dot_center_lt_of_ne T o e.nonzero hT).trans_le (octSupport_le_widths T S e.normal)
  have hsep := e.separates
  rcases abs_lt.mp h₁ with ⟨h₁a,h₁b⟩
  rcases abs_lt.mp h₂ with ⟨h₂a,h₂b⟩
  simp only [dot_sub_right] at *
  exact ⟨by linarith,by linarith⟩

lemma dot_open_bound_of_ne (S : UnitSquare) {n : Point} (hn : n ≠ (0,0))
    {p : Point} (hp : openSquare S p) : |dot n (sub p S.center)| < width S n := by
  have hh := Cert.weighted_strict (abs_nonneg (frameX S n)) (abs_nonneg (frameY S n))
    (frame_abs_sum_pos S hn) hp.1 hp.2
  rw [← frame_dot S]
  change |frameX S n*localX S p+frameY S n*localY S p| < width S n
  have ha := abs_add_le (frameX S n*localX S p) (frameY S n*localY S p)
  rw [abs_mul,abs_mul] at ha
  dsimp [width]
  linarith

/-- Safe extension, directly from ordinary disjointness and the center polygon. -/
theorem safe_openRay_of_disjoint (S T : UnitSquare) (o : Point)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hS : P8 (alpha S o) (beta S o)) (hT : P8 (alpha T o) (beta T o)) :
    Disjoint (openRay S o) {p | openSquare T p} := by
  obtain ⟨e⟩ := separation_exists S T hd
  rw [Set.disjoint_left]
  rintro p ⟨t,ht,q,hq,rfl⟩ hp
  have hsign := e.center_signs o hS hT
  have hmove := mul_nonpos_of_nonneg_of_nonpos ht hsign.1
  have hqB := (abs_lt.mp (dot_open_bound_of_ne S e.nonzero hq)).2
  have hpB := (abs_lt.mp (dot_open_bound_of_ne T e.nonzero hp)).1
  have hsep := e.separates
  simp only [dot_sub_right,dot_add_right,dot_scale_right] at *
  linarith

lemma center_ne_of_strict_octagons (S T : UnitSquare) (o : Point)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hS : P8Strict (alpha S o) (beta S o)) (hT : P8Strict (alpha T o) (beta T o)) :
    S.center ≠ o := by
  obtain ⟨e⟩ := separation_exists S T hd
  have hh := (e.strict_center_signs o hS hT).1
  intro hc
  simp [hc,sub,dot] at hh

end ThreeUnitSquaresInCircle.Unified
