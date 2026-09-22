import ThreeUnitSquaresInCircle.Geometry

/-!
# A size-independent packing model

`PackingN` generalizes `Packing` from `Fin 3` to `Fin n` without adding any
hypothesis. Distances always use `normSq`, not the product-space norm on
`ℝ × ℝ` (which is the maximum norm).
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Unified

/-- The same geometric predicate as `Packing`, for an arbitrary finite family. -/
def PackingN {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))

@[simp] theorem packingN_three (S : Fin 3 → UnitSquare) (o : Point) (R : ℝ) :
    PackingN S o R ↔ Packing S o R := Iff.rfl

/-- Non-overlap, without a containing disk or any lower-bound assumption. -/
def InteriorDisjoint {ι : Type*} (S : ι → UnitSquare) : Prop :=
  ∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p)

lemma PackingN.disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : PackingN S o R) : InteriorDisjoint S := hp.2.2

lemma containing_index_unique {ι : Type*} {S : ι → UnitSquare}
    (hd : InteriorDisjoint S) {i j : ι} {o : Point}
    (hi : openSquare (S i) o) (hj : openSquare (S j) o) : i = j := by
  by_contra hij
  exact hd i j hij o ⟨hi, hj⟩

lemma PackingN.reindex {m n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : PackingN S o R) (e : Fin m ↪ Fin n) :
    PackingN (fun i => S (e i)) o R := by
  refine ⟨hp.1, fun i => hp.2.1 (e i), ?_⟩
  intro i j hij
  exact hp.2.2 (e i) (e j) (fun h => hij (e.injective h))

/-- Nonnegative absolute coordinates of the tested point in a square's frame. -/
def alpha (S : UnitSquare) (o : Point) : ℝ := |localX S o|
def beta (S : UnitSquare) (o : Point) : ℝ := |localY S o|

lemma alpha_nonneg (S : UnitSquare) (o : Point) : 0 ≤ alpha S o := abs_nonneg _
lemma beta_nonneg (S : UnitSquare) (o : Point) : 0 ≤ beta S o := abs_nonneg _

/-- Squared distance to the farthest vertex in local absolute coordinates. -/
def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2

lemma frame_distance (S : UnitSquare) (p o : Point) :
    (localX S p - localX S o)^2 + (localY S p - localY S o)^2 =
      normSq (sub p o) := by
  calc
    _ = (S.cosine^2 + S.sine^2) * normSq (sub p o) := by
      dsimp [localX, localY, normSq, sub]
      ring
    _ = _ := by rw [S.unit]; ring

/-- Containment of the four vertices supplies the exact curved center constraint. -/
lemma phi_le_of_contained (S : UnitSquare) (o : Point) (R : ℝ)
    (h : ∀ p, closedSquare S p → inDisk o R p) :
    phi (alpha S o) (beta S o) ≤ R^2 := by
  have hv (j : Fin 4) :
      ((localVertex j).1 - localX S o)^2 +
        ((localVertex j).2 - localY S o)^2 ≤ R^2 := by
    have hh := h _ (vertex_mem S j)
    rw [inDisk, ← frame_distance S, localX_rotated, localY_rotated] at hh
    exact hh
  by_cases hx : 0 ≤ localX S o <;> by_cases hy : 0 ≤ localY S o
  · have hh := hv 0
    norm_num [localVertex] at hh
    dsimp [phi, alpha, beta]
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    nlinarith only [hh]
  · have hh := hv 1
    norm_num [localVertex] at hh
    dsimp [phi, alpha, beta]
    rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy)]
    nlinarith only [hh]
  · have hh := hv 2
    norm_num [localVertex] at hh
    dsimp [phi, alpha, beta]
    rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy]
    nlinarith only [hh]
  · have hh := hv 3
    norm_num [localVertex] at hh
    dsimp [phi, alpha, beta]
    rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)]
    nlinarith only [hh]

lemma PackingN.phi_le {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : PackingN S o R) (i : Fin n) :
    phi (alpha (S i) o) (beta (S i) o) ≤ R^2 :=
  phi_le_of_contained _ _ _ (hp.2.1 i)

/-- The signed local coordinates of a vector, without translation. -/
def frameX (S : UnitSquare) (v : Point) : ℝ := S.cosine*v.1 + S.sine*v.2
def frameY (S : UnitSquare) (v : Point) : ℝ := -S.sine*v.1 + S.cosine*v.2

lemma frame_norm (S : UnitSquare) (v : Point) :
    (frameX S v)^2 + (frameY S v)^2 = normSq v := by
  calc
    _ = (S.cosine^2 + S.sine^2) * normSq v := by
      dsimp [frameX, frameY, normSq]; ring
    _ = _ := by rw [S.unit]; ring

lemma frame_dot (S : UnitSquare) (v w : Point) :
    frameX S v * frameX S w + frameY S v * frameY S w = dot v w := by
  calc
    _ = (S.cosine^2 + S.sine^2) * dot v w := by
      dsimp [frameX, frameY, dot]; ring
    _ = _ := by rw [S.unit]; ring

lemma frame_centerX (S : UnitSquare) (o : Point) :
    frameX S (sub S.center o) = -localX S o := by
  dsimp [frameX, sub, localX]; ring

lemma frame_centerY (S : UnitSquare) (o : Point) :
    frameY S (sub S.center o) = -localY S o := by
  dsimp [frameY, sub, localY]; ring

lemma abs_frame_centerX (S : UnitSquare) (o : Point) :
    |frameX S (sub S.center o)| = alpha S o := by
  rw [frame_centerX, abs_neg]; rfl

lemma abs_frame_centerY (S : UnitSquare) (o : Point) :
    |frameY S (sub S.center o)| = beta S o := by
  rw [frame_centerY, abs_neg]; rfl

lemma dot_add_right (v p q : Point) : dot v (add p q) = dot v p + dot v q := by
  dsimp [dot, add]; ring
lemma dot_sub_right (v p q : Point) : dot v (sub p q) = dot v p - dot v q := by
  dsimp [dot, sub]; ring
lemma dot_scale_right (v : Point) (t : ℝ) (p : Point) :
    dot v (scale t p) = t * dot v p := by dsimp [dot, scale]; ring

lemma sub_add_cancel_coord (p q : Point) : add (sub p q) q = p := by
  ext <;> dsimp [add, sub] <;> ring

lemma localX_continuous (S : UnitSquare) : Continuous (localX S) := by
  unfold localX; fun_prop
lemma localY_continuous (S : UnitSquare) : Continuous (localY S) := by
  unfold localY; fun_prop
lemma alpha_continuous (S : UnitSquare) : Continuous (alpha S) :=
  (localX_continuous S).abs
lemma beta_continuous (S : UnitSquare) : Continuous (beta S) :=
  (localY_continuous S).abs

end ThreeUnitSquaresInCircle.Unified
