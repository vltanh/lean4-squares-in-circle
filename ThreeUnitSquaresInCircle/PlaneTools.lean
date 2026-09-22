import ThreeUnitSquaresInCircle.CoefficientBridge

/-!
Coordinate transport for independently oriented squares.
Compiles against Lean 4.34.0 / mathlib v4.34.0. No compiler or external decision procedure is invoked.
-/
noncomputable section
namespace ThreeUnitSquaresInCircle.Cert
open RatData

abbrev quarter : ℝ := Real.pi / 2

def aframe (c : Point) (t : ℝ) : UnitSquare where
  center := c
  cosine := Real.cos t
  sine := Real.sin t
  unit := by nlinarith [Real.sin_sq_add_cos_sq t]

def afamily (c : Fin 3 → Point) (t : Fin 3 → ℝ) : Fin 3 → UnitSquare :=
  fun i => aframe (c i) (t i)

def reflection (p : Point) : Point := (p.1, -p.2)

def SameSquare (S T : UnitSquare) : Prop :=
  (∀ p, closedSquare S p ↔ closedSquare T p) ∧
  (∀ p, openSquare S p ↔ openSquare T p)

lemma SameSquare.refl (S : UnitSquare) : SameSquare S S :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

lemma SameSquare.trans {S T U : UnitSquare} (h : SameSquare S T)
    (g : SameSquare T U) : SameSquare S U :=
  ⟨fun p => (h.1 p).trans (g.1 p), fun p => (h.2 p).trans (g.2 p)⟩

lemma packing_replace {S T : Fin 3 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (h : ∀ i, SameSquare (T i) (S i)) : Packing T o R := by
  refine ⟨hp.1, ?_, ?_⟩
  · intro i p hmem
    exact hp.2.1 i p ((h i).1 p |>.mp hmem)
  · intro i j hij p hm
    exact hp.2.2 i j hij p ⟨(h i).2 p |>.mp hm.1, (h j).2 p |>.mp hm.2⟩

lemma packing_reindex {S : Fin 3 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (σ : Fin 3 → Fin 3) (hσ : Function.Injective σ) :
    Packing (fun i => S (σ i)) o R := by
  exact ⟨hp.1, fun i => hp.2.1 (σ i),
    fun i j hij => hp.2.2 (σ i) (σ j) (fun h => hij (hσ h))⟩

@[simp] lemma inDisk_origin (R : ℝ) (p : Point) :
    inDisk (0,0) R p ↔ normSq p ≤ R^2 := by simp [inDisk, sub]

@[simp] lemma rotation_zero (p : Point) : rotation 0 p = p := by
  simp [rotation]

lemma rotation_comp (a b : ℝ) (p : Point) :
    rotation a (rotation b p) = rotation (a+b) p := by
  apply Prod.ext <;> simp only [rotation, Real.cos_add, Real.sin_add] <;> ring

@[simp] lemma rotation_inverse (a : ℝ) (p : Point) :
    rotation (-a) (rotation a p) = p := by rw [rotation_comp]; simp

@[simp] lemma rotation_inverse' (a : ℝ) (p : Point) :
    rotation a (rotation (-a) p) = p := by rw [rotation_comp]; simp

lemma rotation_sub (a : ℝ) (p q : Point) :
    rotation a (sub p q) = sub (rotation a p) (rotation a q) := by
  apply Prod.ext <;> simp only [rotation, sub] <;> ring

lemma rotation_add (a : ℝ) (p q : Point) :
    rotation a (add p q) = add (rotation a p) (rotation a q) := by
  apply Prod.ext <;> simp only [rotation, add] <;> ring

lemma rotation_scale (a r : ℝ) (p : Point) :
    rotation a (scale r p) = scale r (rotation a p) := by
  apply Prod.ext <;> simp only [rotation, scale] <;> ring

@[simp] lemma rotation_normSq (a : ℝ) (p : Point) :
    normSq (rotation a p) = normSq p := by
  exact normSq_rotate (aframe (0,0) a) p

lemma rotation_dot (a : ℝ) (p q : Point) :
    dot (rotation a p) (rotation a q) = dot p q := by
  have h := normSq_add (rotation a p) (rotation a q)
  rw [← rotation_add, rotation_normSq, rotation_normSq, rotation_normSq,
    normSq_add] at h
  linarith

@[simp] lemma reflection_reflection (p : Point) : reflection (reflection p) = p := by
  simp [reflection]

@[simp] lemma reflection_normSq (p : Point) : normSq (reflection p) = normSq p := by
  simp [reflection, normSq]

def coords (c : Point) (t : ℝ) (p : Point) : Point := rotation (-t) (sub p c)

lemma coords_local (c : Point) (t : ℝ) (p : Point) :
    coords c t p = (localX (aframe c t) p, localY (aframe c t) p) := by
  apply Prod.ext <;>
    simp [coords, rotation, sub, localX, localY, aframe, Real.cos_neg, Real.sin_neg]

lemma coords_rotate (c : Point) (t r : ℝ) (p : Point) :
    coords (rotation r c) (r+t) (rotation r p) = coords c t p := by
  unfold coords
  rw [← rotation_sub, rotation_comp]
  congr 1
  ring

lemma frame_rotate_closed (c : Point) (t r : ℝ) (p : Point) :
    closedSquare (aframe (rotation r c) (r+t)) (rotation r p) ↔
      closedSquare (aframe c t) p := by
  have h := coords_rotate c t r p
  rw [coords_local, coords_local] at h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only at hx hy
  simp only [closedSquare, hx, hy]

lemma frame_rotate_open (c : Point) (t r : ℝ) (p : Point) :
    openSquare (aframe (rotation r c) (r+t)) (rotation r p) ↔
      openSquare (aframe c t) p := by
  have h := coords_rotate c t r p
  rw [coords_local, coords_local] at h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only at hx hy
  simp only [openSquare, hx, hy]

lemma packing_rotate_angles {c : Fin 3 → Point} {t : Fin 3 → ℝ} {R : ℝ}
    (hp : Packing (afamily c t) (0,0) R) (r : ℝ) :
    Packing (afamily (fun i => rotation r (c i)) (fun i => r+t i)) (0,0) R := by
  refine ⟨hp.1, ?_, ?_⟩
  · intro i p hmem
    have hm : closedSquare (aframe (c i) (t i)) (rotation (-r) p) := by
      apply (frame_rotate_closed (c i) (t i) r (rotation (-r) p)).mp
      simpa only [rotation_inverse', afamily] using hmem
    have hd := hp.2.1 i _ hm
    simpa only [inDisk_origin, rotation_normSq] using hd
  · intro i j hij p hm
    apply hp.2.2 i j hij (rotation (-r) p)
    constructor
    · apply (frame_rotate_open (c i) (t i) r (rotation (-r) p)).mp
      simpa only [rotation_inverse', afamily] using hm.1
    · apply (frame_rotate_open (c j) (t j) r (rotation (-r) p)).mp
      simpa only [rotation_inverse', afamily] using hm.2

lemma frame_reflect (c : Point) (t : ℝ) (p : Point) :
    (closedSquare (aframe (reflection c) (-t)) (reflection p) ↔
      closedSquare (aframe c t) p) ∧
    (openSquare (aframe (reflection c) (-t)) (reflection p) ↔
      openSquare (aframe c t) p) := by
  have hx : localX (aframe (reflection c) (-t)) (reflection p) =
      localX (aframe c t) p := by
    simp [localX, aframe, reflection, Real.cos_neg, Real.sin_neg]; ring
  have hy : localY (aframe (reflection c) (-t)) (reflection p) =
      -localY (aframe c t) p := by
    simp [localY, aframe, reflection, Real.cos_neg, Real.sin_neg]; ring
  simp only [closedSquare, openSquare, hx, hy, abs_neg, and_self]

lemma packing_reflect_angles {c : Fin 3 → Point} {t : Fin 3 → ℝ} {R : ℝ}
    (hp : Packing (afamily c t) (0,0) R) :
    Packing (afamily (fun i => reflection (c i)) (fun i => -t i)) (0,0) R := by
  refine ⟨hp.1, ?_, ?_⟩
  · intro i p hmem
    have hm : closedSquare (aframe (c i) (t i)) (reflection p) := by
      apply (frame_reflect (c i) (t i) (reflection p)).1.mp
      simpa only [reflection_reflection, afamily] using hmem
    have hd := hp.2.1 i _ hm
    simpa only [inDisk_origin, reflection_normSq] using hd
  · intro i j hij p hm
    apply hp.2.2 i j hij (reflection p)
    constructor
    · apply (frame_reflect (c i) (t i) (reflection p)).2.mp
      simpa only [reflection_reflection, afamily] using hm.1
    · apply (frame_reflect (c j) (t j) (reflection p)).2.mp
      simpa only [reflection_reflection, afamily] using hm.2

lemma frame_quarter_same (c : Point) (t : ℝ) :
    SameSquare (aframe c (t+quarter)) (aframe c t) := by
  have hx (p : Point) : localX (aframe c (t+quarter)) p = localY (aframe c t) p := by
    simp [localX, localY, aframe, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hy (p : Point) : localY (aframe c (t+quarter)) p = -localX (aframe c t) p := by
    simp [localX, localY, aframe, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]; ring
  constructor <;> intro p <;>
    simp only [closedSquare, openSquare, hx, hy, abs_neg, and_comm]

lemma packing_lift_quarters {c : Fin 3 → Point} {t : Fin 3 → ℝ} {R : ℝ}
    (hp : Packing (afamily c t) (0,0) R) (lift : Fin 3 → Bool) :
    Packing (afamily c (fun i => t i + if lift i then quarter else 0)) (0,0) R := by
  apply packing_replace hp
  intro i
  cases h : lift i
  · simpa [afamily, h] using SameSquare.refl (aframe (c i) (t i))
  · simpa [afamily, h] using frame_quarter_same (c i) (t i)

/-- A simultaneous quarter-turn, followed by frame reindexing, moves only the centers. -/
lemma packing_turn_centers {c : Fin 3 → Point} {t : Fin 3 → ℝ} {R : ℝ}
    (hp : Packing (afamily c t) (0,0) R) :
    Packing (afamily (fun i => rotation (-quarter) (c i)) t) (0,0) R := by
  have h := packing_lift_quarters (packing_rotate_angles hp (-quarter)) (fun _ => true)
  have ht : (fun i => (-quarter+t i) + if true = true then quarter else 0) = t := by
    funext i
    simp only [ite_true]
    ring
  rw [ht] at h
  exact h

/-- Reframing a square through 90 degrees does not move its underlying set. -/
def turnFrame (S : UnitSquare) : UnitSquare where
  center := S.center
  cosine := -S.sine
  sine := S.cosine
  unit := by nlinarith [S.unit]

lemma turnFrame_same (S : UnitSquare) : SameSquare (turnFrame S) S := by
  have hx (p : Point) : localX (turnFrame S) p = localY S p := by
    rfl
  have hy (p : Point) : localY (turnFrame S) p = -localX S p := by
    dsimp [localX, localY, turnFrame]; ring
  constructor <;> intro p <;>
    simp only [closedSquare, openSquare, hx, hy, abs_neg, and_comm]

lemma first_quadrant_frame (S : UnitSquare) :
    ∃ T : UnitSquare, SameSquare T S ∧ T.center = S.center ∧
      0 ≤ T.cosine ∧ 0 ≤ T.sine := by
  by_cases hc : 0 ≤ S.cosine
  · by_cases hs : 0 ≤ S.sine
    · exact ⟨S, SameSquare.refl S, rfl, hc, hs⟩
    · refine ⟨turnFrame S, turnFrame_same S, rfl, ?_, ?_⟩
      · dsimp [turnFrame]; linarith
      · exact hc
  · by_cases hs : 0 ≤ S.sine
    · refine ⟨turnFrame (turnFrame (turnFrame S)),
        (turnFrame_same _).trans ((turnFrame_same _).trans (turnFrame_same S)),
        rfl, ?_, ?_⟩
      · simpa [turnFrame] using hs
      · dsimp [turnFrame]; linarith
    · refine ⟨turnFrame (turnFrame S),
        (turnFrame_same _).trans (turnFrame_same S), rfl, ?_, ?_⟩ <;>
        dsimp [turnFrame] <;> linarith

lemma square_angle_representative (S : UnitSquare) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ quarter ∧ SameSquare (aframe S.center t) S := by
  obtain ⟨T, hsame, hcenter, hc, hs⟩ := first_quadrant_frame S
  have hc1 : T.cosine ≤ 1 := by nlinarith [T.unit, sq_nonneg T.sine]
  let t := Real.arccos T.cosine
  have hcos : Real.cos t = T.cosine := Real.cos_arccos (by linarith) hc1
  have ht0 : 0 ≤ t := Real.arccos_nonneg _
  have htpi : t ≤ Real.pi := Real.arccos_le_pi _
  have ht : t ≤ quarter := by
    by_contra hn
    have hlt := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show 0 ≤ quarter by positivity) htpi (lt_of_not_ge hn)
    rw [Real.cos_pi_div_two, hcos] at hlt
    linarith
  have hsin0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 htpi
  have hsin : Real.sin t = T.sine := by
    have hu := Real.sin_sq_add_cos_sq t
    rw [hcos] at hu
    nlinarith [T.unit]
  refine ⟨t, ht0, ht, SameSquare.trans ?_ hsame⟩
  constructor <;> intro p <;>
    simp only [closedSquare, openSquare, localX, localY, aframe, hcos, hsin, hcenter]

lemma frame_translate (c o : Point) (t : ℝ) (p : Point) :
    (closedSquare (aframe (sub c o) t) p ↔ closedSquare (aframe c t) (add p o)) ∧
    (openSquare (aframe (sub c o) t) p ↔ openSquare (aframe c t) (add p o)) := by
  have hx : localX (aframe (sub c o) t) p = localX (aframe c t) (add p o) := by
    dsimp [localX, aframe, sub, add]; ring
  have hy : localY (aframe (sub c o) t) p = localY (aframe c t) (add p o) := by
    dsimp [localY, aframe, sub, add]; ring
  simp only [closedSquare, openSquare, hx, hy, and_self]

lemma packing_angle_representatives {S : Fin 3 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) :
    ∃ (c : Fin 3 → Point) (t : Fin 3 → ℝ),
      (∀ i, 0 ≤ t i ∧ t i ≤ quarter) ∧ Packing (afamily c t) (0,0) R := by
  choose t ht0 ht1 heq using fun i => square_angle_representative (S i)
  let c : Fin 3 → Point := fun i => sub (S i).center o
  refine ⟨c, t, fun i => ⟨ht0 i, ht1 i⟩, hp.1, ?_, ?_⟩
  · intro i p hmem
    have hm := (frame_translate (S i).center o (t i) p).1.mp hmem
    have hd := hp.2.1 i (add p o) ((heq i).1 _ |>.mp hm)
    simpa [inDisk, add, sub] using hd
  · intro i j hij p hm
    apply hp.2.2 i j hij (add p o)
    exact ⟨(heq i).2 _ |>.mp ((frame_translate _ _ _ _).2.mp hm.1),
      (heq j).2 _ |>.mp ((frame_translate _ _ _ _).2.mp hm.2)⟩

end ThreeUnitSquaresInCircle.Cert
