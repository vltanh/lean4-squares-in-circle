import SquaresInCircles.Common.Contacts

/-!
# The centre section of a square in a strip

A unit square that contains the origin, and whose points in the band
`|y| < 1` all have `|x| ≤ 1/2`, is axis-parallel and centred on `x = 0`: a
tilted square has a section through its centre longer than 1.
-/
noncomputable section
namespace SquaresInCircles.Seven.Equality

/-- `(x, y)` lies in the open unit square with centre `(X, Y)` and axes `(c, s)`
and `(-s, c)`. -/
def sectionOpen (c s X Y x y : ℝ) : Prop :=
  |c*(x-X)+s*(y-Y)| < 1/2 ∧ |-s*(x-X)+c*(y-Y)| < 1/2

lemma center_section_forces_cardinal {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (hY : |Y| < 1)
    (hstrip : ∀ x y, sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    c = 0 ∨ s = 0 := by
  by_contra hn
  obtain ⟨hc,hs⟩ := not_or.mp hn
  have hc1 : |c| < 1 := (sq_lt_one_iff_abs_lt_one c).mp (by linarith [sq_pos_of_ne_zero hs])
  have hs1 : |s| < 1 := (sq_lt_one_iff_abs_lt_one s).mp (by linarith [sq_pos_of_ne_zero hc])
  let m := max |c| |s|
  let q := 1/2+(1-m)/4
  have hm1 : m < 1 := max_lt hc1 hs1
  have hq : 1/2 < q := by dsimp [q]; linarith
  have hq0 : 0 < q := by linarith
  have hqm : m*q < 1/2 := by
    have hp := mul_pos (sub_pos.2 hm1) (show 0 < 2-m by linarith)
    dsimp [q]
    linarith
  have hcq : |c| * q < 1/2 := (mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le).trans_lt hqm
  have hsq : |s| * q < 1/2 := (mul_le_mul_of_nonneg_right (le_max_right _ _) hq0.le).trans_lt hqm
  have hin (d : ℝ) (hd : |d| = q) : |X+d| ≤ 1/2 :=
    hstrip _ Y (by simpa [sectionOpen,abs_mul,hd] using And.intro hcq hsq) hY
  linarith [(abs_le.mp (hin q (abs_of_pos hq0))).2,
    (abs_le.mp (hin (-q) (by rw [abs_neg,abs_of_pos hq0]))).1]

/-- A unit square whose open section contains the origin, and whose points in
the band `|y| < 1` all have `|x| ≤ 1/2`, is axis-parallel and centred at
`(0, Y)` with `|Y| < 1/2`. -/
theorem section_strip_rigidity {c s X Y : ℝ}
    (hunit : c^2+s^2=1) (h0 : sectionOpen c s X Y 0 0)
    (hstrip : ∀ x y, sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    |Y| < 1/2 ∧ ∀ x y, sectionOpen c s X Y x y ↔ openAxisSquare (0,Y) x y := by
  have hid : (c*(0-X)+s*(0-Y))^2+(-s*(0-X)+c*(0-Y))^2 = X^2+Y^2 := by
    linear_combination (X^2+Y^2)*hunit
  have h1 := sq_lt_sq' (abs_lt.mp h0.1).1 (abs_lt.mp h0.1).2
  have h2 := sq_lt_sq' (abs_lt.mp h0.2).1 (abs_lt.mp h0.2).2
  have hY : |Y| < 1 := (sq_lt_one_iff_abs_lt_one Y).mp (by linarith [sq_nonneg X])
  have hrect (x y : ℝ) : sectionOpen c s X Y x y ↔ |x-X| < 1/2 ∧ |y-Y| < 1/2 :=
    cardinal_box hunit (center_section_forces_cardinal hunit hY hstrip)
  have hin (x : ℝ) (hx : |x-X| < 1/2) : |x| ≤ 1/2 :=
    hstrip x Y ((hrect x Y).mpr ⟨hx,by simp⟩) hY
  have hxpos : X+1/2 ≤ 1/2 := affine_endpoint_le (A := X) fun t ht0 ht1 => by
    linarith [(abs_le.mp (hin (X+t/2) (abs_lt.mpr ⟨by linarith,by linarith⟩))).2]
  have hxneg : -X+1/2 ≤ 1/2 := affine_endpoint_le (A := -X) fun t ht0 ht1 => by
    linarith [(abs_le.mp (hin (X-t/2) (abs_lt.mpr ⟨by linarith,by linarith⟩))).1]
  obtain rfl : X = 0 := by linarith
  exact ⟨by simpa using ((hrect 0 0).mp h0).2,hrect⟩

end SquaresInCircles.Seven.Equality
