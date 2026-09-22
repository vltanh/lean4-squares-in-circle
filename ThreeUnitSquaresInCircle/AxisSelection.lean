import ThreeUnitSquaresInCircle.SeparatingAxes

/-! Transport the two-square separating axes and normalize the first cardinal index. -/
noncomputable section
namespace ThreeUnitSquaresInCircle.Cert
open RatData

lemma frame_move_open (c o : Point) (t r : ℝ) (p : Point) :
    openSquare (aframe (add o (rotation r c)) (r+t)) (add o (rotation r p)) ↔
      openSquare (aframe c t) p := by
  have hs : sub (add o (rotation r p)) (add o (rotation r c)) =
      rotation r (sub p c) := by
    rw [rotation_sub]
    apply Prod.ext <;> dsimp [sub,add] <;> ring
  have hco : coords (add o (rotation r c)) (r+t) (add o (rotation r p)) =
      coords c t p := by
    unfold coords
    rw [hs,rotation_comp]
    congr 1
    ring
  rw [coords_local,coords_local] at hco
  have hx := congrArg Prod.fst hco
  have hy := congrArg Prod.snd hco
  simp only at hx hy
  simp only [openSquare,hx,hy]

lemma opposite_cardinal (k : Fin 4) :
    castPoint (dirs (k+2)) = scale (-1) (castPoint (dirs k)) := by
  fin_cases k <;> norm_num [dirs,castPoint,scale]

lemma signed_pair_axis (c₀ c₁ : Point) (θ φ : ℝ)
    (hδ0 : 0 ≤ φ-θ) (hδ1 : φ-θ ≤ Real.pi/3)
    (hdisj : ∀ p, ¬ (openSquare (aframe c₀ θ) p ∧ openSquare (aframe c₁ φ) p)) :
    ∃ (pick : Bool) (k : Fin 4),
      halfWidth (φ-θ) ≤ dot
        (rotation (if pick then φ else θ) (castPoint (dirs k))) (sub c₁ c₀) := by
  let d := rotation (-θ) (sub c₁ c₀)
  have hdrot : rotation θ d = sub c₁ c₀ := rotation_inverse' θ _
  have hcenter : add c₀ (rotation θ d) = c₁ := by
    rw [hdrot]
    apply Prod.ext <;> dsimp [add,sub] <;> ring
  have hzero : add c₀ (rotation θ (0,0)) = c₀ := by simp [rotation,add]
  have hn : ∀ p, ¬ (openSquare (aframe (0,0) 0) p ∧ openSquare (aframe d (φ-θ)) p) := by
    intro p hp
    apply hdisj (add c₀ (rotation θ p))
    constructor
    · have hm := (frame_move_open (0,0) c₀ 0 θ p).mpr hp.1
      simpa only [hzero,add_zero] using hm
    · have hm := (frame_move_open d c₀ (φ-θ) θ p).mpr hp.2
      simpa only [hcenter,show θ+(φ-θ)=φ by ring] using hm
  have ha := axis_separation_zero d (φ-θ) hδ0 hδ1 hn
  have hproj (r : ℝ) (k : Fin 4) :
      dot (rotation r (castPoint (dirs k))) (sub c₁ c₀) =
        dot (rotation (r-θ) (castPoint (dirs k))) d := by
    calc
      _ = dot (rotation (-θ) (rotation r (castPoint (dirs k))))
          (rotation (-θ) (sub c₁ c₀)) := (rotation_dot (-θ) _ _).symm
      _ = _ := by rw [rotation_comp]; congr 2; ring
  have hu : ∃ (pick : Bool) (k : Fin 4),
      halfWidth (φ-θ) ≤ |dot
        (rotation (if pick then φ else θ) (castPoint (dirs k))) (sub c₁ c₀)| := by
    rcases ha with h | h | h | h
    · refine ⟨false,0,?_⟩
      rw [hproj]
      simpa [rotation,castPoint,dirs,dot] using h
    · refine ⟨false,1,?_⟩
      rw [hproj]
      simpa [rotation,castPoint,dirs,dot] using h
    · refine ⟨true,0,?_⟩
      rw [hproj]
      simpa [rotation,castPoint,dirs,dot] using h
    · refine ⟨true,1,?_⟩
      rw [hproj]
      simpa [rotation,castPoint,dirs,dot] using h
  obtain ⟨pick,k,hk⟩ := hu
  by_cases hp : 0 ≤ dot (rotation (if pick then φ else θ) (castPoint (dirs k))) (sub c₁ c₀)
  · exact ⟨pick,k,by simpa only [abs_of_nonneg hp] using hk⟩
  · refine ⟨pick,k+2,?_⟩
    rw [opposite_cardinal,rotation_scale]
    have hn : dot (scale (-1) (rotation (if pick then φ else θ) (castPoint (dirs k))))
        (sub c₁ c₀) = -dot (rotation (if pick then φ else θ) (castPoint (dirs k)))
          (sub c₁ c₀) := by dsimp [dot,scale]; ring
    rw [hn]
    simpa only [abs_of_neg (lt_of_not_ge hp)] using hk

lemma raw_separating_axes (c : Fin 3 → Point) (x : Point) (R : ℝ)
    (hx : AngleDomain.Domain x.1 x.2)
    (hp : Packing (angularSquares c x) (0,0) R) :
    ∃ (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3),
      (∀ e, s e = first e ∨ s e = last e) ∧
      (∀ e, widths x e ≤ dot (normal x k s e)
        (sub (c (edgeEnd e)) (c (edgeStart e)))) := by
  have H (e : Fin 3) : ∃ (s : Fin 3) (k : Fin 4),
      (s = first e ∨ s = last e) ∧
      widths x e ≤ dot (rotation (theta x s) (castPoint (dirs k)))
        (sub (c (edgeEnd e)) (c (edgeStart e))) := by
    have he : theta x (edgeEnd e)-theta x (edgeStart e) = arguments x e := by
      fin_cases e <;> norm_num [theta,arguments,edgeStart,edgeEnd]
    have hr := argument_ranges hx e
    have hu : arguments x e ≤ Real.pi/3 := by
      apply hr.2.trans
      fin_cases e <;> norm_num <;> linarith [Real.pi_pos]
    have hne : edgeStart e ≠ edgeEnd e := by fin_cases e <;> decide
    obtain ⟨pick,k,hsep⟩ := signed_pair_axis (c (edgeStart e)) (c (edgeEnd e))
      (theta x (edgeStart e)) (theta x (edgeEnd e))
      (by rw [he]; exact hr.1) (by rw [he]; exact hu)
      (hp.2.2 (edgeStart e) (edgeEnd e) hne)
    rw [he] at hsep
    cases pick
    · refine ⟨edgeStart e,k,?_,?_⟩
      · left; fin_cases e <;> rfl
      · simpa [widths] using hsep
    · refine ⟨edgeEnd e,k,?_,?_⟩
      · right; fin_cases e <;> rfl
      · simpa [widths] using hsep
  choose s k hs hsep using H
  exact ⟨k,s,hs,hsep⟩

lemma packing_nat_turn_centers {c : Fin 3 → Point} {t : Fin 3 → ℝ} {R : ℝ}
    (hp : Packing (afamily c t) (0,0) R) (j : ℕ) :
    Packing (afamily (fun i => rotation (-(j:ℝ)*quarter) (c i)) t) (0,0) R := by
  induction j with
  | zero => simpa only [Nat.cast_zero,neg_zero,zero_mul,rotation_zero] using hp
  | succ j ih =>
    have h := packing_turn_centers ih
    have he : (fun i => rotation (-quarter) (rotation (-(j:ℝ)*quarter) (c i))) =
        (fun i => rotation (-((j+1:ℕ):ℝ)*quarter) (c i)) := by
      funext i
      rw [rotation_comp]
      congr 1
      push_cast
      ring
    simpa only [he] using h

lemma negative_quarter_rotation (j : Fin 4) (p : Point) :
    rotation (-(j.val:ℝ)*quarter) p =
      (![p,(p.2,-p.1),(-p.1,-p.2),(-p.2,p.1)] : Fin 4 → Point) j := by
  fin_cases j
  · simp [rotation]
  · norm_num [rotation,quarter,Real.cos_neg,Real.sin_neg]
  · have he : -(2:ℝ)*quarter = -Real.pi := by ring
    simp [he,rotation,Real.cos_neg,Real.sin_neg]
  · have he : -(3:ℝ)*quarter = -(Real.pi+Real.pi/2) := by ring
    simp [he,rotation,Real.cos_neg,Real.sin_neg,Real.cos_add,Real.sin_add]

lemma rotation_commute (a b : ℝ) (p : Point) :
    rotation a (rotation b p) = rotation b (rotation a p) := by
  rw [rotation_comp,rotation_comp,add_comm a b]

lemma quarter_normal (j k : Fin 4) (t : ℝ) :
    rotation (-(j.val:ℝ)*quarter) (rotation t (castPoint (dirs k))) =
      rotation t (castPoint (dirs (k-j))) := by
  rw [rotation_commute,negative_quarter_rotation]
  congr 1
  fin_cases j <;> fin_cases k <;> norm_num [dirs,castPoint]

/-- Choose the edge normals and make the first cardinal index zero. -/
theorem choose_separating_axes (c : Fin 3 → Point) (x : Point) (R : ℝ)
    (hx : AngleDomain.Domain x.1 x.2)
    (hp : Packing (angularSquares c x) (0,0) R) :
    ∃ (c' : Fin 3 → Point) (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3),
      Packing (angularSquares c' x) (0,0) R ∧ k 0 = 0 ∧
      (∀ e, s e = first e ∨ s e = last e) ∧
      (∀ e, widths x e ≤ dot (normal x k s e)
        (sub (c' (edgeEnd e)) (c' (edgeStart e)))) := by
  obtain ⟨k,s,hs,hsep⟩ := raw_separating_axes c x R hx hp
  let r : ℝ := -((k 0).val:ℝ)*quarter
  let c' : Fin 3 → Point := fun i => rotation r (c i)
  let k' : Fin 3 → Fin 4 := fun e => k e-k 0
  have hp' : Packing (angularSquares c' x) (0,0) R := by
    exact packing_nat_turn_centers hp (k 0).val
  refine ⟨c',k',s,hp',by simp [k'],hs,?_⟩
  intro e
  have hn : normal x k' s e = rotation r (normal x k s e) := by
    exact (quarter_normal (k 0) (k e) (theta x (s e))).symm
  rw [hn]
  change widths x e ≤ dot (rotation r (normal x k s e))
    (sub (rotation r (c (edgeEnd e))) (rotation r (c (edgeStart e))))
  rw [← rotation_sub,rotation_dot]
  exact hsep e

end ThreeUnitSquaresInCircle.Cert
