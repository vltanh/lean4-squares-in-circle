import SquaresInCircles.Common.Basic
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# A supporting functional for two squares with disjoint interiors

Open squares are convex and open, so the geometric Hahn--Banach theorem
separates two squares with disjoint interiors by a nonzero linear functional
`dot n`. `support_separator` sharpens this to the exact support bound
`width S n + width T n ≤ dot n (sub T.center S.center)` by testing the
functional on shrunk support vertices, which lie in the open squares. No
separating-axis enumeration is assumed.
-/

noncomputable section
namespace SquaresInCircles

lemma weighted_strict {a b u v H : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a+b) (hu : u < H) (hv : v < H) :
    a*u+b*v < H*(a+b) := by
  have h₁ := mul_nonneg ha (sub_nonneg.mpr hu.le)
  have h₂ := mul_nonneg hb (sub_nonneg.mpr hv.le)
  by_cases hapos : 0 < a
  · have h := mul_pos hapos (sub_pos.mpr hu)
    linarith
  · have hbpos : 0 < b := by linarith
    have h := mul_pos hbpos (sub_pos.mpr hv)
    linarith

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

/-- Half the width of a square in the direction `n`, in units of `|n|`. -/
def width (S : UnitSquare) (n : Point) : ℝ :=
  (|frameX S n|+|frameY S n|)/2

lemma width_neg (S : UnitSquare) (n : Point) :
    width S (scale (-1) n) = width S n := by
  have h₁ : frameX S (scale (-1) n) = -frameX S n := by dsimp [frameX,scale]; ring
  have h₂ : frameY S (scale (-1) n) = -frameY S n := by dsimp [frameY,scale]; ring
  simp only [width,h₁,h₂,abs_neg]

lemma signed_half_product (X t : ℝ) :
    X*(if 0 ≤ X then t/2 else -t/2) = t*|X|/2 := by
  split_ifs with hX
  · rw [abs_of_nonneg hX]; ring
  · rw [abs_of_neg (lt_of_not_ge hX)]; ring

/-- Shrunk support vertices lie in the open square, even when a coefficient is zero. -/
lemma support_point (S : UnitSquare) (n : Point) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ p : Point, openSquare S p ∧
      dot n p = dot n S.center+t*width S n := by
  let X := frameX S n
  let Y := frameY S n
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
        dsimp [dot,add,rotate,X,Y,frameX,frameY]; ring
      _ = dot n S.center+t*|X|/2+t*|Y|/2 := by
        dsimp [q]
        rw [signed_half_product,signed_half_product]
      _ = dot n S.center+t*width S n := by
        dsimp [width,X,Y]; ring

lemma bound_from_shrinks {H D : ℝ}
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

/-- A nonzero functional that separates two squares by their full widths. -/
structure Separation (S T : UnitSquare) where
  normal : Point
  nonzero : normal ≠ (0,0)
  separates : width S normal+width T normal ≤ dot normal (sub T.center S.center)

/-- A nonzero supporting functional for two squares with disjoint open interiors. -/
theorem support_separator (S T : UnitSquare)
    (hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    Nonempty (Separation S T) := by
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
  refine ⟨⟨n,hn,bound_from_shrinks ?_⟩⟩
  intro t ht0 ht1
  obtain ⟨p,hp,hpval⟩ := support_point S n ht0 ht1
  obtain ⟨q,hq,hqval⟩ := support_point T (scale (-1) n) ht0 ht1
  have hsep := lt_trans (hS p hp) (hT q hq)
  rw [hf,hf,hpval] at hsep
  rw [width_neg] at hqval
  simp only [dot,scale,neg_one_mul] at hqval
  dsimp [dot,sub] at hsep ⊢
  linarith

end SquaresInCircles
