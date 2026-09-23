import SquaresInCircles.Geometry

/-!
# Frames, interior-disjointness and the farthest-vertex bound

Vector operations, a square's frame and vertices, and the squared distance
`phi` from a point to the farthest vertex of a square. Distances always use
`normSq`, not the product-space norm on `ℝ × ℝ` (which is the maximum norm).
-/
noncomputable section
namespace SquaresInCircles

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
def add (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)
def scale (t : ℝ) (p : Point) : Point := (t * p.1, t * p.2)

lemma normSq_nonneg (p : Point) : 0 ≤ normSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

def rotate (S : UnitSquare) (p : Point) : Point :=
  (S.cosine * p.1 - S.sine * p.2,
   S.sine * p.1 + S.cosine * p.2)

lemma localX_rotated (S : UnitSquare) (p : Point) :
    localX S (add S.center (rotate S p)) = p.1 := by
  calc
    _ = p.1 * (S.cosine ^ 2 + S.sine ^ 2) := by
      simp only [localX, add, rotate]
      ring
    _ = p.1 := by rw [S.unit]; ring

lemma localY_rotated (S : UnitSquare) (p : Point) :
    localY S (add S.center (rotate S p)) = p.2 := by
  calc
    _ = p.2 * (S.cosine ^ 2 + S.sine ^ 2) := by
      simp only [localY, add, rotate]
      ring
    _ = p.2 := by rw [S.unit]; ring

def localVertex : Fin 4 → Point :=
  ![(-1 / 2, -1 / 2), (-1 / 2, 1 / 2), (1 / 2, -1 / 2), (1 / 2, 1 / 2)]

lemma vertex_mem (S : UnitSquare) (j : Fin 4) :
    closedSquare S (add S.center (rotate S (localVertex j))) := by
  unfold closedSquare
  rw [localX_rotated, localY_rotated]
  fin_cases j <;> norm_num [localVertex]

/-- Non-overlap, without a containing disk or any lower-bound assumption. -/
def InteriorDisjoint {ι : Type*} (S : ι → UnitSquare) : Prop :=
  ∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p)

lemma Packing.disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : InteriorDisjoint S := hp.2.2

lemma InteriorDisjoint.pairwise {ι : Type*} {S : ι → UnitSquare}
    (hd : InteriorDisjoint S) :
    Pairwise (fun i j => Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p}) :=
  fun i j hij => Set.disjoint_left.mpr fun p hi hj => hd i j hij p ⟨hi,hj⟩

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
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  norm_num [localVertex] at h0 h1 h2 h3
  dsimp [phi,alpha,beta]
  rcases abs_cases (localX S o) with ⟨hx,-⟩ | ⟨hx,-⟩ <;>
    rcases abs_cases (localY S o) with ⟨hy,-⟩ | ⟨hy,-⟩ <;> rw [hx,hy] <;> linarith

lemma Packing.phi_le {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (i : Fin n) :
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

lemma normSq_pos_of_ne {v : Point} (hv : v ≠ (0,0)) : 0 < normSq v := by
  have hn := normSq_nonneg v
  by_contra hh
  apply hv
  apply Prod.ext <;> dsimp [normSq] at * <;>
    nlinarith [sq_nonneg v.1,sq_nonneg v.2]

lemma sub_ne_origin {p q : Point} (h : p ≠ q) : sub p q ≠ (0,0) := by
  intro hh
  apply h
  have hx := congrArg Prod.fst hh
  have hy := congrArg Prod.snd hh
  apply Prod.ext <;> dsimp [sub] at * <;> linarith

lemma small_disk_in_openSquare (S : UnitSquare) {p : Point}
    (hp : normSq (sub p S.center) < 1/4) : openSquare S p := by
  have hu := frame_norm S (sub p S.center)
  change (localX S p)^2+(localY S p)^2=normSq (sub p S.center) at hu
  exact ⟨abs_lt.mpr ⟨by nlinarith [sq_nonneg (localY S p)],
                         by nlinarith [sq_nonneg (localY S p)]⟩,
         abs_lt.mpr ⟨by nlinarith [sq_nonneg (localX S p)],
                         by nlinarith [sq_nonneg (localX S p)]⟩⟩

def halfDiagonal : ℝ := Real.sqrt 2/2

lemma halfDiagonal_pos : 0 < halfDiagonal := by unfold halfDiagonal; positivity
lemma halfDiagonal_sq : halfDiagonal^2=1/2 := by
  have hh := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  dsimp [halfDiagonal]
  linarith
lemma halfDiagonal_gt_707 : (707:ℝ)/1000 < halfDiagonal := by
  nlinarith [halfDiagonal_sq,halfDiagonal_pos]

lemma local_center_norm (S : UnitSquare) (o : Point) :
    normSq (sub S.center o)=(alpha S o)^2+(beta S o)^2 := by
  have h := frame_norm S (sub S.center o)
  rw [frame_centerX,frame_centerY] at h
  simpa only [alpha,beta,sq_abs,neg_sq] using h.symm

end SquaresInCircles
