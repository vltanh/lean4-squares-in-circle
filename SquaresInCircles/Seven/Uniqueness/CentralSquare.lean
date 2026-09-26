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

lemma side_barriers_cover {x y : ℝ} (hx : |x| = 1/2) (hy : |y| ≤ 1) :
    ∃ i : Fin 4, closedAxisSquare (sideCenters i) x y := by
  rw [abs_le] at hy
  rcases (abs_eq (by norm_num)).mp hx with rfl | rfl <;> rcases le_total 0 y with h | h <;>
    [exists 1; exists 0; exists 3; exists 2] <;>
    exact ⟨by norm_num [sideCenters],
      abs_le.mpr ⟨by simp [sideCenters]; linarith,by simp [sideCenters]; linarith⟩⟩

lemma central_strip {S : UnitSquare} {B : Fin 4 → UnitSquare} {o : Point} {φ : Direction}
    (h0 : openSquare S o) (hrep : ∀ i, Represents (B i) o φ (sideCenters i))
    (hd : ∀ i p, ¬ (openSquare (B i) p ∧ openSquare S p)) :
    ∀ x y, openSquare S (pointInDirection o φ x y) → |y| < 1 → |x| ≤ 1/2 := by
  intro x y hp hy
  by_contra! hx
  set t := 1/(2*|x|)
  have ht0 : 0 < t := by positivity
  have ht1 : t < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have he : (1-t) • o+t • pointInDirection o φ x y = pointInDirection o φ (t*x) (t*y) := by
    ext <;> simp [pointInDirection] <;> ring
  have hp' : openSquare S (pointInDirection o φ (t*x) (t*y)) :=
    he ▸ openSquare_convex S h0 hp (by linarith) ht0.le (by ring)
  have htx : |t*x| = 1/2 := by rw [abs_mul,abs_of_pos ht0]; simp only [t]; field_simp
  have hty : |t*y| ≤ 1 := by
    rw [abs_mul,abs_of_pos ht0]
    exact (mul_le_of_le_one_left (abs_nonneg y) ht1.le).trans hy.le
  obtain ⟨i,hi⟩ := side_barriers_cover htx hty
  exact closed_open_disjoint (B i) S (hd i) (((hrep i).closed _ _).mpr hi) hp'

/-- The open square `S` read in the frame of `o` and `φ`. -/
lemma square_section (S : UnitSquare) (o : Point) (φ : Direction) (x y : ℝ) :
    openSquare S (pointInDirection o φ x y) ↔
    sectionOpen (relativeC (modelSquare o φ 0) S) (relativeS (modelSquare o φ 0) S)
      (frameX (modelSquare o φ 0) (sub S.center o))
      (frameY (modelSquare o φ 0) (sub S.center o)) x y := by
  have hu := Real.Angle.cos_sq_add_sin_sq φ
  simp only [openSquare,sectionOpen]
  congr! 3 <;>
    dsimp [localX,localY,pointInDirection,relativeC,relativeS,frameX,frameY,sub,modelSquare]
  · linear_combination (S.cosine*(S.center.1-o.1)+S.sine*(S.center.2-o.2))*hu
  · linear_combination (S.cosine*(S.center.2-o.2)-S.sine*(S.center.1-o.1))*hu

/-- The square that contains the disk centre sits at `(0, z)`, with
`|z| < 1/2`, in the frame of the four side squares. -/
theorem central_square_represents {S : UnitSquare} {B : Fin 4 → UnitSquare}
    {o : Point} {φ : Direction} (h0 : openSquare S o)
    (hrep : ∀ i, Represents (B i) o φ (sideCenters i))
    (hd : ∀ i p, ¬ (openSquare (B i) p ∧ openSquare S p)) :
    ∃ z : ℝ, |z| < 1/2 ∧ Represents S o φ (0,z) := by
  have hs := square_section S o φ
  obtain ⟨hz,hr⟩ := section_strip_rigidity (relative_unit _ S)
    ((hs 0 0).mp (by simpa [pointInDirection] using h0))
    (fun x y hxy hy => central_strip h0 hrep hd x y ((hs x y).mpr hxy) hy)
  exact ⟨_,hz,fun x y => (hs x y).trans (hr x y)⟩

end Equality
end SquaresInCircles.Seven
