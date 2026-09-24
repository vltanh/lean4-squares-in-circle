import SquaresInCircles.Common.NormalForm

/-!
# A width-one strip fixes the frame of an origin-containing unit square

The proof uses the horizontal section THROUGH THE SQUARE CENTER. The center
lies strictly inside |y|<1 because the square contains the origin. A tilted
unit square has a center section wider than one, contradicting the strip.
No trigonometric approximation or vertical-centering hypothesis is needed.
-/
noncomputable section
namespace SquaresInCircles.Seven.Equality

def sectionOpen (c s X Y x y : ℝ) : Prop :=
  |c*(x-X)+s*(y-Y)| < 1/2 ∧ |-s*(x-X)+c*(y-Y)| < 1/2

lemma section_origin_center_bound {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (h0 : sectionOpen c s X Y 0 0) : X^2+Y^2 < 1/2 := by
  have hid : (c*(-X)+s*(-Y))^2+(-s*(-X)+c*(-Y))^2 = X^2+Y^2 := by
    calc
      _ = (c^2+s^2)*(X^2+Y^2) := by ring
      _ = _ := by rw [hunit]; ring
  rcases abs_lt.mp h0.1 with ⟨hx0,hx1⟩
  rcases abs_lt.mp h0.2 with ⟨hy0,hy1⟩
  dsimp [sectionOpen] at hx0 hx1 hy0 hy1
  have hxsq : (c*(-X)+s*(-Y))^2 < 1/4 := by nlinarith
  have hysq : (-s*(-X)+c*(-Y))^2 < 1/4 := by nlinarith
  linarith

lemma center_section_forces_cardinal {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (hY : |Y| < 1)
    (hstrip : ∀ x y, sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    c = 0 ∨ s = 0 := by
  by_contra hn
  have hc : c ≠ 0 := by intro he; exact hn (Or.inl he)
  have hs : s ≠ 0 := by intro he; exact hn (Or.inr he)
  have hc1 : |c| < 1 := by nlinarith [sq_abs c,abs_nonneg c,sq_pos_of_ne_zero hs]
  have hs1 : |s| < 1 := by nlinarith [sq_abs s,abs_nonneg s,sq_pos_of_ne_zero hc]
  let m := max |c| |s|
  let q := 1/2+(1-m)/4
  have hm0 : 0 ≤ m := (abs_nonneg c).trans (le_max_left _ _)
  have hm1 : m < 1 := max_lt hc1 hs1
  have hq : 1/2 < q := by dsimp [q]; linarith
  have hqm : q*m < 1/2 := by
    have hp := mul_pos (show 0 < 1-m by linarith) (show 0 < 2-m by linarith)
    dsimp [q]
    nlinarith
  have hcq : |c|*q < 1/2 := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left |c| |s|) (show 0 ≤ q by linarith)
    change |c|*q ≤ m*q at hh
    nlinarith
  have hsq : |s|*q < 1/2 := by
    have hh := mul_le_mul_of_nonneg_right (le_max_right |c| |s|) (show 0 ≤ q by linarith)
    change |s|*q ≤ m*q at hh
    nlinarith
  have hplus : sectionOpen c s X Y (X+q) Y := by
    simpa [sectionOpen,abs_mul,abs_of_pos (show 0 < q by linarith)] using And.intro hcq hsq
  have hminus : sectionOpen c s X Y (X-q) Y := by
    simpa [sectionOpen,abs_mul,abs_of_pos (show 0 < q by linarith)] using And.intro hcq hsq
  have hp := abs_le.mp (hstrip (X+q) Y hplus hY)
  have hm := abs_le.mp (hstrip (X-q) Y hminus hY)
  linarith

lemma cardinal_section {c s X Y x y : ℝ}
    (hunit : c^2+s^2=1) (hcard : c = 0 ∨ s = 0) :
    sectionOpen c s X Y x y ↔ |x-X| < 1/2 ∧ |y-Y| < 1/2 := by
  rcases hcard with hc | hs
  · rw [hc] at hunit
    have he : s = 1 ∨ s = -1 := by nlinarith
    rcases he with rfl | rfl <;> simp [sectionOpen,hc,and_comm]
  · rw [hs] at hunit
    have he : c = 1 ∨ c = -1 := by nlinarith
    rcases he with rfl | rfl <;> simp [sectionOpen,hs]

/-- The only possible center freedom is the vertical coordinate. -/
theorem section_strip_rigidity {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (h0 : sectionOpen c s X Y 0 0)
    (hstrip : ∀ x y, sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    X = 0 ∧ c*s = 0 ∧ |Y| < 1/2 ∧
      ∀ x y, sectionOpen c s X Y x y ↔ |x| < 1/2 ∧ |y-Y| < 1/2 := by
  have hbound := section_origin_center_bound hunit h0
  have hY : |Y| < 1 := abs_lt.mpr
    ⟨by nlinarith [sq_nonneg X],by nlinarith [sq_nonneg X]⟩
  have hcard := center_section_forces_cardinal hunit hY hstrip
  have hrect (x y : ℝ) := cardinal_section (X := X) (Y := Y) (x := x) (y := y) hunit hcard
  have hxpos : X+1/2 ≤ 1/2 := by
    apply affine_endpoint_le (A := X)
    intro t ht0 ht1
    have hm : sectionOpen c s X Y (X+t/2) Y := (hrect _ _).mpr (by
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith)
    have hh := (abs_le.mp (hstrip _ _ hm hY)).2
    nlinarith
  have hxneg : -X+1/2 ≤ 1/2 := by
    apply affine_endpoint_le (A := -X)
    intro t ht0 ht1
    have hm : sectionOpen c s X Y (X-t/2) Y := (hrect _ _).mpr (by
      constructor <;> apply abs_lt.mpr <;> constructor <;> linarith)
    have hh := (abs_le.mp (hstrip _ _ hm hY)).1
    nlinarith
  have hx : X = 0 := by linarith
  have hc : c*s = 0 := by rcases hcard with h | h <;> simp [h]
  have hy : |Y| < 1/2 := by
    have hh := (hrect 0 0).mp h0
    simpa using hh.2
  refine ⟨hx,hc,hy,?_⟩
  intro x y
  simpa only [hx,sub_zero] using hrect x y

end SquaresInCircles.Seven.Equality
