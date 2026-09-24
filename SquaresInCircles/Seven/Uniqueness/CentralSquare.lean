import SquaresInCircles.Seven.Uniqueness.CenterSection

/-!
# The square in the middle

The four side squares block the band `|y| ≤ 1` beyond `|x| = 1/2`, so the
square that contains the disk centre stays in the strip between them, and by
`CenterSection` it is axis-parallel and centred on the axis. Its height is
left free.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

def sideCenters : Fin 4 → Point :=
  ![(1,-1/2),(1,1/2),(-1,-1/2),(-1,1/2)]

lemma open_segment (S : UnitSquare) {p q : Point}
    (hp : openSquare S p) (hq : openSquare S q) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) : openSquare S (add (scale (1-t) p) (scale t q)) := by
  have he := local_affine S p q t
  have hnon : 0 ≤ 1-t := by linarith [ht.2]
  have scalar (x y : ℝ) (hx : |x| < 1/2) (hy : |y| < 1/2) :
      |(1-t)*x+t*y| < 1/2 := by
    have hh := abs_add_le ((1-t)*x) (t*y)
    rw [abs_mul,abs_mul,abs_of_nonneg hnon,abs_of_nonneg ht.1] at hh
    by_cases ht0 : t = 0
    · simpa [ht0] using hx
    · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have ha := mul_le_mul_of_nonneg_left hx.le hnon
      have hb := mul_lt_mul_of_pos_left hy htp
      nlinarith
  exact ⟨by rw [he.1]; exact scalar _ _ hp.1 hq.1,
    by rw [he.2]; exact scalar _ _ hp.2 hq.2⟩

lemma side_barriers_cover {x y : ℝ} (hx : 1/2 ≤ |x| ∧ |x| ≤ 3/2)
    (hy : |y| ≤ 1) : ∃ i : Fin 4, closedAxisSquare (sideCenters i) x y := by
  have hya := abs_le.mp hy
  by_cases hxn : 0 ≤ x <;> by_cases hyn : 0 ≤ y
  · refine ⟨1,?_⟩
    rw [abs_of_nonneg hxn] at hx
    dsimp [closedAxisSquare,sideCenters]
    exact ⟨abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩,
      abs_le.mpr ⟨by linarith,by linarith [hya.2]⟩⟩
  · refine ⟨0,?_⟩
    rw [abs_of_nonneg hxn] at hx
    dsimp [closedAxisSquare,sideCenters]
    exact ⟨abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩,
      abs_le.mpr ⟨by linarith [hya.1],by linarith⟩⟩
  · refine ⟨3,?_⟩
    rw [abs_of_neg (lt_of_not_ge hxn)] at hx
    dsimp [closedAxisSquare,sideCenters]
    exact ⟨abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩,
      abs_le.mpr ⟨by linarith,by linarith [hya.2]⟩⟩
  · refine ⟨2,?_⟩
    rw [abs_of_neg (lt_of_not_ge hxn)] at hx
    dsimp [closedAxisSquare,sideCenters]
    exact ⟨abs_le.mpr ⟨by linarith [hx.2],by linarith [hx.1]⟩,
      abs_le.mpr ⟨by linarith [hya.1],by linarith⟩⟩

lemma central_strip {S : UnitSquare} {B : Fin 4 → UnitSquare} {o : Point} {φ : Direction}
    (h0 : openSquare S o) (hrep : ∀ i, Represents (B i) o φ (sideCenters i))
    (hd : ∀ i p, ¬ (openSquare (B i) p ∧ openSquare S p)) :
    ∀ x y, openSquare S (pointInDirection o φ x y) → |y| < 1 → |x| ≤ 1/2 := by
  intro x y hp hy
  by_contra hn
  have hx : 1/2 < |x| := lt_of_not_ge hn
  let z := (1/2+min |x| 1)/2
  have hz0 : 1/2 < z := by
    have hh : 1/2 < min |x| 1 := lt_min hx (by norm_num)
    dsimp [z]
    linarith
  have hz1 : z ≤ 3/4 := by
    have hh := min_le_right |x| (1 : ℝ)
    dsimp [z]
    linarith
  have hzx : z < |x| := by
    have hh := min_le_left |x| (1 : ℝ)
    dsimp [z]
    linarith
  let t := z/|x|
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith : 0 < |x|)).mpr hzx
  have hp' := open_segment S h0 hp ⟨ht0.le,ht1.le⟩
  have he : add (scale (1-t) o) (scale t (pointInDirection o φ x y)) =
      pointInDirection o φ (t*x) (t*y) := by
    apply Prod.ext <;> dsimp [add,scale,pointInDirection] <;> ring
  rw [he] at hp'
  have htx : |t*x| = z := by
    rw [abs_mul,abs_of_pos ht0]
    dsimp [t]
    field_simp [ne_of_gt (show 0 < |x| by linarith)]
  have hty : |t*y| < 1 := by
    rw [abs_mul,abs_of_pos ht0]
    have hle := mul_le_mul_of_nonneg_right ht1.le (abs_nonneg y)
    nlinarith
  obtain ⟨i,hi⟩ := side_barriers_cover
    (x := t*x) (y := t*y) ⟨by rw [htx]; linarith,by rw [htx]; linarith⟩ hty.le
  have hc : closedSquare (B i) (pointInDirection o φ (t*x) (t*y)) :=
    ((hrep i).closed _ _).mpr hi
  exact closed_open_disjoint (B i) S (hd i) hc hp'

/-- The centre of `S` in the frame of `o` and `φ`. -/
def centerX (S : UnitSquare) (o : Point) (φ : Direction) : ℝ :=
  φ.cos*(S.center.1-o.1)+φ.sin*(S.center.2-o.2)
def centerY (S : UnitSquare) (o : Point) (φ : Direction) : ℝ :=
  -φ.sin*(S.center.1-o.1)+φ.cos*(S.center.2-o.2)
def frameCos (S : UnitSquare) (φ : Direction) : ℝ := φ.cos*S.cosine+φ.sin*S.sine
def frameSin (S : UnitSquare) (φ : Direction) : ℝ := φ.cos*S.sine-φ.sin*S.cosine

lemma relative_frame_unit (S : UnitSquare) (φ : Direction) :
    frameCos S φ^2+frameSin S φ^2 = 1 := by
  calc
    _ = (φ.cos^2+φ.sin^2)*(S.cosine^2+S.sine^2) := by dsimp [frameCos,frameSin]; ring
    _ = 1 := by rw [Real.Angle.cos_sq_add_sin_sq,S.unit]; ring

lemma frame_center_constants (S : UnitSquare) (o : Point) (φ : Direction) :
    frameCos S φ*centerX S o φ+frameSin S φ*centerY S o φ = -localX S o ∧
    -frameSin S φ*centerX S o φ+frameCos S φ*centerY S o φ = -localY S o := by
  constructor
  · calc
      _ = (φ.cos^2+φ.sin^2)*(-localX S o) := by
        dsimp [frameCos,frameSin,centerX,centerY,localX]; ring
      _ = _ := by rw [Real.Angle.cos_sq_add_sin_sq]; ring
  · calc
      _ = (φ.cos^2+φ.sin^2)*(-localY S o) := by
        dsimp [frameCos,frameSin,centerX,centerY,localY]; ring
      _ = _ := by rw [Real.Angle.cos_sq_add_sin_sq]; ring

lemma square_section (S : UnitSquare) (o : Point) (φ : Direction) (x y : ℝ) :
    openSquare S (pointInDirection o φ x y) ↔
    sectionOpen (frameCos S φ) (frameSin S φ) (centerX S o φ) (centerY S o φ) x y := by
  have hx : localX S (pointInDirection o φ x y) =
      frameCos S φ*x+frameSin S φ*y+localX S o := by
    dsimp [localX,pointInDirection,frameCos,frameSin]; ring
  have hy : localY S (pointInDirection o φ x y) =
      -frameSin S φ*x+frameCos S φ*y+localY S o := by
    dsimp [localY,pointInDirection,frameCos,frameSin]; ring
  have hc := frame_center_constants S o φ
  have hx' : localX S (pointInDirection o φ x y) =
      frameCos S φ*(x-centerX S o φ)+frameSin S φ*(y-centerY S o φ) := by
    rw [hx]
    nlinarith [hc.1]
  have hy' : localY S (pointInDirection o φ x y) =
      -frameSin S φ*(x-centerX S o φ)+frameCos S φ*(y-centerY S o φ) := by
    rw [hy]
    nlinarith [hc.2]
  simp only [openSquare,sectionOpen,hx',hy']

/-- The square that contains the disk centre sits at `(0, z)`, with
`|z| < 1/2`, in the frame of the four side squares. -/
theorem central_square_represents {S : UnitSquare} {B : Fin 4 → UnitSquare}
    {o : Point} {φ : Direction} (h0 : openSquare S o)
    (hrep : ∀ i, Represents (B i) o φ (sideCenters i))
    (hd : ∀ i p, ¬ (openSquare (B i) p ∧ openSquare S p)) :
    ∃ z : ℝ, |z| < 1/2 ∧ Represents S o φ (0,z) := by
  have hc0 : sectionOpen (frameCos S φ) (frameSin S φ)
      (centerX S o φ) (centerY S o φ) 0 0 := by
    apply (square_section S o φ 0 0).mp
    simpa [pointInDirection] using h0
  have hstrip := central_strip h0 hrep hd
  have hr := section_strip_rigidity (relative_frame_unit S φ) hc0
    (fun x y hxy hy => hstrip x y ((square_section S o φ x y).mpr hxy) hy)
  refine ⟨centerY S o φ,hr.2.2.1,?_⟩
  intro x y
  rw [square_section,hr.2.2.2 x y]
  simp [openAxisSquare]

end Equality
end SquaresInCircles.Seven
