import ThreeUnitSquaresInCircle.Unified.Tangents
import ThreeUnitSquaresInCircle.SeparatingAxes

/-!
# Safe radial extension, for any number of squares

Only `Cert.support_separator` is reused from the existing geometric proof.
The separator need not be an edge normal. The octagon support bound works for
EVERY normal, because the octagon lies in the Minkowski sum of its square and
an inscribed disk of radius 1/2. The proof below is coordinate algebra.
-/

noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

abbrev frameX (S : UnitSquare) (p : Point) := S.cosine*p.1 + S.sine*p.2
abbrev frameY (S : UnitSquare) (p : Point) := -S.sine*p.1 + S.cosine*p.2
abbrev halfSupport := Cert.supportRadius

theorem frame_norm (S : UnitSquare) (p : Point) :
    frameX S p ^ 2 + frameY S p ^ 2 = normSq p := by
  calc
    _ = (S.cosine^2 + S.sine^2) * normSq p := by
      dsimp [frameX, frameY, normSq]; ring
    _ = _ := by rw [S.unit]; ring

theorem dot_in_frame (S : UnitSquare) (p q : Point) :
    dot p q = frameX S p * frameX S q + frameY S p * frameY S q := by
  calc
    _ = (S.cosine^2 + S.sine^2) * dot p q := by rw [S.unit]; ring
    _ = _ := by dsimp [dot, frameX, frameY]; ring

theorem normal_coordinates_positive {S : UnitSquare} {n : Point}
    (hn : n ≠ origin) : 0 < |frameX S n| + |frameY S n| := by
  have hnorm := frame_norm S n
  have hx := abs_nonneg (frameX S n)
  have hy := abs_nonneg (frameY S n)
  by_contra h
  have hx0 : frameX S n = 0 := abs_eq_zero.mp (by linarith)
  have hy0 : frameY S n = 0 := abs_eq_zero.mp (by linarith)
  have hn1 : n.1 = 0 := by
    rw [hx0, hy0] at hnorm
    dsimp [normSq] at hnorm
    nlinarith [sq_nonneg n.2]
  have hn2 : n.2 = 0 := by
    rw [hx0, hy0] at hnorm
    dsimp [normSq] at hnorm
    nlinarith [sq_nonneg n.1]
  exact hn (Prod.ext hn1 hn2)

theorem halfSupport_pos {S : UnitSquare} {n : Point} (hn : n ≠ origin) :
    0 < halfSupport S n := by
  have h := normal_coordinates_positive (S := S) hn
  change 0 < (|frameX S n| + |frameY S n|)/2
  linarith

/-- The l1 norm of a normal in one frame bounds each component in another. -/
theorem other_frame_bound (S T : UnitSquare) (n : Point) :
    |frameX S n| ≤ |frameX T n| + |frameY T n| ∧
    |frameY S n| ≤ |frameX T n| + |frameY T n| := by
  have hS := frame_norm S n
  have hT := frame_norm T n
  have hp := mul_nonneg (abs_nonneg (frameX T n)) (abs_nonneg (frameY T n))
  constructor <;>
    nlinarith [sq_abs (frameX S n), sq_abs (frameY S n),
      sq_abs (frameX T n), sq_abs (frameY T n),
      abs_nonneg (frameX S n), abs_nonneg (frameY S n),
      abs_nonneg (frameX T n), abs_nonneg (frameY T n),
      sq_nonneg (frameX S n), sq_nonneg (frameY S n)]

def octSupport (x y : ℝ) : ℝ := max (max x y) (3*(x+y)/4)

theorem octagon_bilinear {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : Octagon a b) : x*a + y*b ≤ octSupport x y := by
  by_cases hxy : 3*y ≤ x
  · have ht : x*a+y*b ≤ x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hb,
        mul_nonneg hx (sub_nonneg.mpr h.1)]
    exact ht.trans ((le_max_left x y).trans (le_max_left _ _))
  · by_cases hyx : 3*x ≤ y
    · have ht : x*a+y*b ≤ y := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hyx) ha,
          mul_nonneg hy (sub_nonneg.mpr h.2)]
      exact ht.trans ((le_max_right x y).trans (le_max_left _ _))
    · have ht : x*a+y*b ≤ 3*(x+y)/4 := by
        have h₁ := mul_nonneg (show 0 ≤ 3*x-y by linarith)
          (sub_nonneg.mpr h.1)
        have h₂ := mul_nonneg (show 0 ≤ 3*y-x by linarith)
          (sub_nonneg.mpr h.2)
        nlinarith
      exact ht.trans (le_max_right _ _)

theorem octagon_bilinear_strict {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxypos : 0 < x+y) (h : OctagonStrict a b) :
    x*a + y*b < octSupport x y := by
  by_cases hxy : 3*y ≤ x
  · have hxp : 0 < x := by linarith
    have ht : x*a+y*b < x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hb,
        mul_pos hxp (sub_pos.mpr h.1)]
    exact ht.trans_le ((le_max_left x y).trans (le_max_left _ _))
  · by_cases hyx : 3*x ≤ y
    · have hyp : 0 < y := by linarith
      have ht : x*a+y*b < y := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hyx) ha,
          mul_pos hyp (sub_pos.mpr h.2)]
      exact ht.trans_le ((le_max_right x y).trans (le_max_left _ _))
    · have ht : x*a+y*b < 3*(x+y)/4 := by
        have h₁ := mul_pos (show 0 < 3*x-y by linarith) (sub_pos.mpr h.1)
        have h₂ := mul_pos (show 0 < 3*y-x by linarith) (sub_pos.mpr h.2)
        nlinarith
      exact ht.trans_le (le_max_right _ _)

theorem octSupport_le_halfSupports (S T : UnitSquare) (n : Point) :
    octSupport |frameX S n| |frameY S n| ≤ halfSupport S n + halfSupport T n := by
  obtain ⟨hx, hy⟩ := other_frame_bound S T n
  dsimp [octSupport, halfSupport, Cert.supportRadius]
  apply max_le
  · apply max_le <;> linarith [abs_nonneg (frameX S n), abs_nonneg (frameY S n)]
  · linarith

theorem dot_center_abs_bound (S : UnitSquare) (o n : Point) :
    dot n (sub S.center o) ≤
      |frameX S n| * alpha S o + |frameY S n| * beta S o := by
  have hx : frameX S (sub S.center o) = -localX S o := by
    dsimp [frameX, sub, localX]; ring
  have hy : frameY S (sub S.center o) = -localY S o := by
    dsimp [frameY, sub, localY]; ring
  rw [dot_in_frame S, hx, hy]
  calc
    _ ≤ |frameX S n * (-localX S o)| + |frameY S n * (-localY S o)| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = _ := by simp [abs_mul, abs_neg, alpha, beta]

theorem center_support_le (S T : UnitSquare) (o n : Point)
    (hS : CenterBody Octagon S o) :
    dot n (sub S.center o) ≤ halfSupport S n + halfSupport T n := by
  exact (dot_center_abs_bound S o n).trans
    ((octagon_bilinear (alpha_nonneg S o) (beta_nonneg S o)
      (abs_nonneg _) (abs_nonneg _) hS).trans (octSupport_le_halfSupports S T n))

theorem center_support_lt (S T : UnitSquare) (o n : Point)
    (hn : n ≠ origin) (hS : CenterBody OctagonStrict S o) :
    dot n (sub S.center o) < halfSupport S n + halfSupport T n := by
  exact (dot_center_abs_bound S o n).trans_lt
    ((octagon_bilinear_strict (alpha_nonneg S o) (beta_nonneg S o)
      (abs_nonneg _) (abs_nonneg _) (normal_coordinates_positive hn) hS).trans_le
        (octSupport_le_halfSupports S T n))

theorem point_support_le (S : UnitSquare) (n p : Point) (hp : closedSquare S p) :
    dot n p ≤ dot n S.center + halfSupport S n := by
  have he : dot n p - dot n S.center =
      frameX S n * localX S p + frameY S n * localY S p := by
    calc
      _ = dot n (sub p S.center) := by dsimp [dot, sub]; ring
      _ = frameX S n * frameX S (sub p S.center) +
          frameY S n * frameY S (sub p S.center) := dot_in_frame S n _
      _ = _ := by dsimp [frameX, frameY, sub, localX, localY]; ring
  have hb : frameX S n * localX S p + frameY S n * localY S p ≤
      |frameX S n|*|localX S p| + |frameY S n|*|localY S p| := by
    simpa [abs_mul] using add_le_add
      (le_abs_self (frameX S n * localX S p))
      (le_abs_self (frameY S n * localY S p))
  have hx := mul_le_mul_of_nonneg_left hp.1 (abs_nonneg (frameX S n))
  have hy := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg (frameY S n))
  change dot n p ≤ dot n S.center + (|frameX S n|+|frameY S n|)/2
  linarith

theorem point_support_lt (S : UnitSquare) (n p : Point) (hn : n ≠ origin)
    (hp : openSquare S p) : dot n p < dot n S.center + halfSupport S n := by
  have he : dot n p - dot n S.center =
      frameX S n * localX S p + frameY S n * localY S p := by
    calc
      _ = dot n (sub p S.center) := by dsimp [dot, sub]; ring
      _ = frameX S n * frameX S (sub p S.center) +
          frameY S n * frameY S (sub p S.center) := dot_in_frame S n _
      _ = _ := by dsimp [frameX, frameY, sub, localX, localY]; ring
  have hb : frameX S n * localX S p + frameY S n * localY S p ≤
      |frameX S n|*|localX S p| + |frameY S n|*|localY S p| := by
    simpa [abs_mul] using add_le_add
      (le_abs_self (frameX S n * localX S p))
      (le_abs_self (frameY S n * localY S p))
  have hw := Cert.weighted_strict (abs_nonneg (frameX S n))
    (abs_nonneg (frameY S n)) (normal_coordinates_positive hn) hp.1 hp.2
  change dot n p < dot n S.center + (|frameX S n|+|frameY S n|)/2
  linarith

def RadialExtension (S : UnitSquare) (o : Point) : Set Point :=
  {p | ∃ q t, closedSquare S q ∧ 0 ≤ t ∧ p = add q (scale t (sub S.center o))}

/-- The target square's center constraint alone ensures safety. -/
theorem radial_extension_safe (S T : UnitSquare) (o : Point)
    (hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hT : CenterBody Octagon T o) :
    Disjoint (RadialExtension S o) {p | openSquare T p} := by
  obtain ⟨n, hn, hsep⟩ := Cert.support_separator S T hdisj
  have hc := center_support_le T S o n hT
  have hdir : dot n (sub S.center o) ≤ 0 := by
    dsimp [dot, sub] at hsep hc ⊢
    linarith
  rw [Set.disjoint_left]
  rintro p ⟨q, t, hq, ht, rfl⟩ hp
  have hqbound := point_support_le S n q hq
  have hnneg : scale (-1) n ≠ origin := by
    intro he
    apply hn
    apply Prod.ext
    · have hh := congrArg Prod.fst he
      simpa [scale, origin] using hh
    · have hh := congrArg Prod.snd he
      simpa [scale, origin] using hh
  have hpbound := point_support_lt T (scale (-1) n) _ hnneg hp
  rw [Cert.supportRadius_neg] at hpbound
  have htdir := mul_nonpos_of_nonneg_of_nonpos ht hdir
  dsimp [dot, sub, add, scale] at hsep hqbound hpbound htdir ⊢
  nlinarith

/-- In a strict relaxation, a square centered at O has no disjoint neighbor. -/
theorem centered_impossible (S T : UnitSquare) (o : Point)
    (hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hT : CenterBody OctagonStrict T o) (hc : S.center = o) : False := by
  obtain ⟨n, hn, hsep⟩ := Cert.support_separator S T hdisj
  have hb := center_support_lt T S o n hn hT
  rw [hc] at hsep
  linarith

end ThreeUnitSquaresInCircle.Unified
