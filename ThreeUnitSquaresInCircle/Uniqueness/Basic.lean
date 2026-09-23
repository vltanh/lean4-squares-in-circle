import ThreeUnitSquaresInCircle.Unified.ThreeCoordinates

/-!
# Geometric normal forms, not equality of frame records

Additive uniqueness development against main d7fa1f3.  These new proof scripts
have not been compiled.  A normal form specifies both open and closed square
sets in one Euclidean frame and includes a permutation of the squares.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Uniqueness
open Unified

abbrev OpenRect (c : Point) (x y : ℝ) : Prop :=
  |x-c.1| < 1/2 ∧ |y-c.2| < 1/2
abbrev ClosedRect (c : Point) (x y : ℝ) : Prop :=
  |x-c.1| ≤ 1/2 ∧ |y-c.2| ≤ 1/2

/-- The actual square, expressed in one common positively oriented frame. -/
def Represents (S : UnitSquare) (o : Point) (φ : Direction) (c : Point) : Prop :=
  ∀ x y, openSquare S (pointInDirection o φ x y) ↔ OpenRect c x y

/-- A rigid motion with its inverse written in coordinates. -/
def frameEquiv (o : Point) (φ : Direction) : Point ≃ Point where
  toFun p := pointInDirection o φ p.1 p.2
  invFun p := (φ.cos*(p.1-o.1)+φ.sin*(p.2-o.2),
    -φ.sin*(p.1-o.1)+φ.cos*(p.2-o.2))
  left_inv := by
    intro p
    have hu := Real.Angle.cos_sq_add_sin_sq φ
    apply Prod.ext <;> dsimp [pointInDirection] <;>
      nlinarith only [congrArg (fun t : ℝ => t*p.1) hu,
        congrArg (fun t : ℝ => t*p.2) hu]
  right_inv := by
    intro p
    have hu := Real.Angle.cos_sq_add_sin_sq φ
    apply Prod.ext <;> dsimp [pointInDirection] <;>
      nlinarith only [congrArg (fun t : ℝ => t*(p.1-o.1)) hu,
        congrArg (fun t : ℝ => t*(p.2-o.2)) hu]

@[simp] lemma frameEquiv_apply (o : Point) (φ : Direction) (p : Point) :
    frameEquiv o φ p = pointInDirection o φ p.1 p.2 := rfl

lemma frameEquiv_zero (o : Point) (φ : Direction) : frameEquiv o φ (0,0)=o := by
  simp [pointInDirection]

lemma frameEquiv_distance (o : Point) (φ : Direction) (p q : Point) :
    normSq (sub (frameEquiv o φ p) (frameEquiv o φ q))=normSq (sub p q) := by
  calc
    _ = (φ.cos^2+φ.sin^2)*normSq (sub p q) := by
      rw [frameEquiv_apply,frameEquiv_apply]
      dsimp [pointInDirection,normSq,sub]; ring
    _ = _ := by rw [Real.Angle.cos_sq_add_sin_sq]; ring

/-- A scalar endpoint is obtained from all strict convex combinations. -/
lemma affine_endpoint_le {A B D : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t < 1 → (1-t)*A+t*B ≤ D) : B ≤ D := by
  have hA : A ≤ D := by simpa using h 0 (by norm_num) (by norm_num)
  by_contra hn
  have hB : D < B := lt_of_not_ge hn
  have hBA : 0 < B-A := by linarith
  let u := (D-A)/(B-A)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) hBA.le
  have hu1 : u < 1 := (div_lt_one hBA).mpr (by linarith)
  have hh := h ((u+1)/2) (by linarith) (by linarith)
  have he : (1-(u+1)/2)*A+((u+1)/2)*B=(D+B)/2 := by
    dsimp [u]; field_simp; ring
  rw [he] at hh
  linarith

lemma local_affine (S : UnitSquare) (p q : Point) (t : ℝ) :
    localX S (add (scale (1-t) p) (scale t q))=(1-t)*localX S p+t*localX S q ∧
    localY S (add (scale (1-t) p) (scale t q))=(1-t)*localY S p+t*localY S q := by
  constructor <;> dsimp [localX,localY,add,scale] <;> ring

lemma shrink_open (S : UnitSquare) {p : Point} (hp : closedSquare S p)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    openSquare S (add (scale (1-t) S.center) (scale t p)) := by
  have he := local_affine S S.center p t
  have hx0 : localX S S.center=0 := by simp [localX]
  have hy0 : localY S S.center=0 := by simp [localY]
  simp only [hx0,hy0,mul_zero,zero_add] at he
  have hX : |t*localX S p| < 1/2 := by
    rw [abs_mul,abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hp.1 ht0).trans_lt (by linarith)
  have hY : |t*localY S p| < 1/2 := by
    rw [abs_mul,abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hp.2 ht0).trans_lt (by linarith)
  exact ⟨by rw [he.1]; exact hX,by rw [he.2]; exact hY⟩

/-- Equality of open squares implies equality of their closed square sets. -/
lemma same_open_same_closed (S T : UnitSquare)
    (h : ∀ p, openSquare S p ↔ openSquare T p) :
    ∀ p, closedSquare S p ↔ closedSquare T p := by
  have oneWay (S T : UnitSquare) (hh : ∀ p, openSquare S p → openSquare T p)
      (p : Point) (hp : closedSquare S p) : closedSquare T p := by
    have hm (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :=
      hh _ (shrink_open S hp ht0 ht1)
    have hX : localX T p ≤ 1/2 := by
      apply affine_endpoint_le (A := localX T S.center)
      intro t ht0 ht1
      have hu := (abs_lt.mp (hm t ht0 ht1).1).2.le
      rw [(local_affine T S.center p t).1] at hu
      exact hu
    have hX' : -localX T p ≤ 1/2 := by
      apply affine_endpoint_le (A := -localX T S.center)
      intro t ht0 ht1
      have hu := (abs_lt.mp (hm t ht0 ht1).1).1.le
      rw [(local_affine T S.center p t).1] at hu
      linarith
    have hY : localY T p ≤ 1/2 := by
      apply affine_endpoint_le (A := localY T S.center)
      intro t ht0 ht1
      have hu := (abs_lt.mp (hm t ht0 ht1).2).2.le
      rw [(local_affine T S.center p t).2] at hu
      exact hu
    have hY' : -localY T p ≤ 1/2 := by
      apply affine_endpoint_le (A := -localY T S.center)
      intro t ht0 ht1
      have hu := (abs_lt.mp (hm t ht0 ht1).2).1.le
      rw [(local_affine T S.center p t).2] at hu
      linarith
    exact ⟨abs_le.mpr ⟨by linarith,hX⟩,abs_le.mpr ⟨by linarith,hY⟩⟩
  intro p
  exact ⟨oneWay S T (fun q => (h q).mp) p,
    oneWay T S (fun q => (h q).mpr) p⟩

def modelSquare (o : Point) (φ : Direction) (c : Point) : UnitSquare where
  center := pointInDirection o φ c.1 c.2
  cosine := φ.cos
  sine := φ.sin
  unit := Real.Angle.cos_sq_add_sin_sq φ

lemma modelSquare_local (o : Point) (φ : Direction) (c : Point) (x y : ℝ) :
    localX (modelSquare o φ c) (pointInDirection o φ x y)=x-c.1 ∧
    localY (modelSquare o φ c) (pointInDirection o φ x y)=y-c.2 := by
  have hu := Real.Angle.cos_sq_add_sin_sq φ
  constructor <;> dsimp [localX,localY,modelSquare,pointInDirection] <;>
    nlinarith only [congrArg (fun t : ℝ => t*(x-c.1)) hu,
      congrArg (fun t : ℝ => t*(y-c.2)) hu]

lemma Represents.closed {S : UnitSquare} {o : Point} {φ : Direction} {c : Point}
    (h : Represents S o φ c) (x y : ℝ) :
    closedSquare S (pointInDirection o φ x y) ↔ ClosedRect c x y := by
  have hopen : ∀ p, openSquare S p ↔ openSquare (modelSquare o φ c) p := by
    intro p
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    have hm := modelSquare_local o φ c q.1 q.2
    rw [frameEquiv_apply]
    simp only [openSquare,hm.1,hm.2]
    exact h q.1 q.2
  have hc := same_open_same_closed S (modelSquare o φ c) hopen
  simpa only [closedSquare,(modelSquare_local o φ c x y).1,
    (modelSquare_local o φ c x y).2] using hc (pointInDirection o φ x y)

/-- Normal form in one Euclidean frame, including the input disk center. -/
def HasNormalForm {n : ℕ} (S : Fin n → UnitSquare) (o : Point)
    (centers : Fin n → Point) : Prop :=
  ∃ (φ : Direction) (σ : Equiv.Perm (Fin n)), ∀ i x y,
    (openSquare (S (σ i)) (pointInDirection o φ x y) ↔ OpenRect (centers i) x y) ∧
    (closedSquare (S (σ i)) (pointInDirection o φ x y) ↔ ClosedRect (centers i) x y)

def threeCenters : Fin 3 → Point := ![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]
def fourCenters : Fin 4 → Point := ![(1/2,1/2),(-1/2,1/2),(-1/2,-1/2),(1/2,-1/2)]
def fiveCenters : Fin 5 → Point := ![(0,0),(1,0),(0,1),(-1,0),(0,-1)]

/-- Non-overlap turns any assignment to the model's slots into a permutation. -/
lemma normal_form_of_slots {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    {φ : Direction} {c : Fin n → Point} (hd : InteriorDisjoint S)
    (h : ∀ i, ∃ j, Represents (S i) o φ (c j)) : HasNormalForm S o c := by
  classical
  choose f hf using h
  have hi : Function.Injective f := by
    intro i j hij
    by_contra hne
    let z := pointInDirection o φ (c (f i)).1 (c (f i)).2
    have hz₁ : openSquare (S i) z := (hf i _ _).mpr (by simp [OpenRect])
    have hz₂ : openSquare (S j) z := (hf j _ _).mpr (by rw [← hij]; simp [OpenRect])
    exact hd i j hne z ⟨hz₁,hz₂⟩
  let e := Equiv.ofBijective f hi.bijective_of_finite
  refine ⟨φ,e.symm,?_⟩
  intro i x y
  have hh : Represents (S (e.symm i)) o φ (c i) := by
    simpa only [show f (e.symm i)=i from e.apply_symm_apply i] using hf (e.symm i)
  exact ⟨hh x y,hh.closed x y⟩

/-- The normal form supplies an explicit Euclidean rigid equivalence. -/
lemma HasNormalForm.rigid_witness {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    {c : Fin n → Point} (h : HasNormalForm S o c) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, closedSquare (S (σ i)) (e p) ↔ ClosedRect (c i) p.1 p.2) := by
  obtain ⟨φ,σ,hφ⟩ := h
  exact ⟨frameEquiv o φ,σ,frameEquiv_zero o φ,frameEquiv_distance o φ,
    fun i p => (hφ i p.1 p.2).2⟩

lemma chart_represents {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    Represents S o C.phase (C.a,C.signedB) := C.cartesian

lemma p3_chart {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hp : P3 (alpha S o) (beta S o)) : P3 C.a C.b := by
  rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simpa only [ha,hb] using hp
  · simpa only [ha,hb] using p3_swap hp

lemma chart_phi {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {K : ℝ} (h : phi (alpha S o) (beta S o) ≤ K) : phi C.a C.b ≤ K := by
  rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · simpa only [ha,hb] using h
  · simpa only [ha,hb,phi,add_comm] using h

end ThreeUnitSquaresInCircle.Uniqueness
