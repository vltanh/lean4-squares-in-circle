import ThreeUnitSquaresInCircle.Geometry

/-!
# The quadratic dual certificate inequality

The main theorem here is an algebraic inequality. It permits arbitrary
centers, offsets, and separating normals. It does not assume that those
normals can always be chosen, nor that a certificate is large enough.
Status: compiles against Lean 4.34.0 / mathlib v4.34.0.
-/

noncomputable section
open scoped BigOperators
namespace ThreeUnitSquaresInCircle

/-- Completing two scalar squares, with a strictly positive coefficient. -/
theorem quadratic_lower (w : ℝ) (hw : 0 < w) (c z : Point) :
    -(normSq z / w) ≤ w * normSq c + 2 * dot c z := by
  rw [← neg_div, div_le_iff₀ hw]
  have hx := sq_nonneg (w * c.1 + z.1)
  have hy := sq_nonneg (w * c.2 + z.2)
  dsimp [normSq, dot] at *
  nlinarith

/-- Summed version; the last hypothesis is the weighted primal inequality. -/
theorem summed_quadratic_lower {n : ℕ} (r2 K : ℝ)
    (w : Fin n → ℝ) (c z : Fin n → Point)
    (hw : ∀ i, 0 < w i)
    (hprimal : K + ∑ i, (w i * normSq (c i) + 2 * dot (c i) (z i)) ≤ r2) :
    K - ∑ i, normSq (z i) / w i ≤ r2 := by
  have hsum :
      (∑ i, -(normSq (z i) / w i)) ≤
      ∑ i, (w i * normSq (c i) + 2 * dot (c i) (z i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact quadratic_lower (w i) (hw i) (c i) (z i)
  rw [Finset.sum_neg_distrib] at hsum
  linarith

def mass {n : ℕ} (lam : Fin n → ℝ) : ℝ := ∑ j, lam j

def moment {n : ℕ} (lam : Fin n → ℝ) (v : Fin n → Point) : Point :=
  (∑ j, lam j * (v j).1, ∑ j, lam j * (v j).2)

lemma weighted_vertex_identity {n : ℕ} (c : Point)
    (v : Fin n → Point) (lam : Fin n → ℝ)
    (hv : ∀ j, normSq (v j) = 1 / 2) :
    (∑ j, lam j * normSq (add c (v j))) =
      mass lam * normSq c + 2 * dot c (moment lam v) + (1 / 2) * mass lam := by
  calc
    _ = ∑ j, (lam j * normSq c +
        (2 * c.1) * (lam j * (v j).1) +
        (2 * c.2) * (lam j * (v j).2) + (1 / 2) * lam j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [normSq_add, hv j]
      dsimp [dot]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      dsimp [mass, moment, dot]
      ring

def edgeStart : Fin 3 → Fin 3 := ![0, 0, 1]
def edgeEnd : Fin 3 → Fin 3 := ![1, 2, 2]

def force (mu : Fin 3 → ℝ) (n : Fin 3 → Point) : Fin 3 → Point :=
  ![add (scale (mu 0) (n 0)) (scale (mu 1) (n 1)),
    add (scale (-mu 0) (n 0)) (scale (mu 2) (n 2)),
    add (scale (-mu 1) (n 1)) (scale (-mu 2) (n 2))]

lemma force_identity (c n : Fin 3 → Point) (mu : Fin 3 → ℝ) :
    (∑ i, dot (c i) (force mu n i)) =
      -(∑ e, mu e * dot (n e) (sub (c (edgeEnd e)) (c (edgeStart e)))) := by
  simp [Fin.sum_univ_succ, force, edgeStart, edgeEnd, dot, add, sub, scale]; ring

def zVector (v : Fin 3 → Fin 4 → Point)
    (lam : Fin 3 → Fin 4 → ℝ) (mu : Fin 3 → ℝ) (n : Fin 3 → Point)
    (i : Fin 3) : Point :=
  add (moment (lam i) (v i)) (scale (1 / 2) (force mu n i))

def dualValue (v : Fin 3 → Fin 4 → Point)
    (lam : Fin 3 → Fin 4 → ℝ) (mu h : Fin 3 → ℝ) (n : Fin 3 → Point) : ℝ :=
  1 / 2 + (∑ e, mu e * h e) -
    ∑ i, normSq (zVector v lam mu n i) / mass (lam i)

lemma energy_identity (c : Fin 3 → Point) (v : Fin 3 → Fin 4 → Point)
    (lam : Fin 3 → Fin 4 → ℝ) (mu : Fin 3 → ℝ) (n : Fin 3 → Point) :
    (∑ i, (mass (lam i) * normSq (c i) + 2 * dot (c i) (zVector v lam mu n i))) =
      (∑ i, (mass (lam i) * normSq (c i) + 2 * dot (c i) (moment (lam i) (v i)))) +
      ∑ i, dot (c i) (force mu n i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [zVector, dot, add, scale]
  ring

/-- The weighted quadratic certificate bound, from explicit vertex and
separation hypotheses. -/
theorem three_square_dual (r2 : ℝ) (c : Fin 3 → Point)
    (v : Fin 3 → Fin 4 → Point) (n : Fin 3 → Point)
    (lam : Fin 3 → Fin 4 → ℝ) (mu h : Fin 3 → ℝ)
    (hlam : ∀ i j, 0 ≤ lam i j)
    (hsum : (∑ i, ∑ j, lam i j) = 1)
    (hw : ∀ i, 0 < mass (lam i))
    (hmu : ∀ e, 0 ≤ mu e)
    (hv : ∀ i j, normSq (v i j) = 1 / 2)
    (hdisk : ∀ i j, normSq (add (c i) (v i j)) ≤ r2)
    (hsep : ∀ e, h e ≤ dot (n e) (sub (c (edgeEnd e)) (c (edgeStart e)))) :
    dualValue v lam mu h n ≤ r2 := by
  have hweighted : (∑ i, ∑ j, lam i j * normSq (add (c i) (v i j))) ≤ r2 := by
    calc
      _ ≤ ∑ i, ∑ j, lam i j * r2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hdisk i j) (hlam i j)
      _ = r2 := by
        simp only [← Finset.sum_mul]
        rw [hsum]
        ring
  have hexpand (i : Fin 3) := weighted_vertex_identity (c i) (v i) (lam i) (hv i)
  have htotal : (∑ i, mass (lam i)) = 1 := hsum
  have hweighted' :
      (1 / 2 : ℝ) +
        (∑ i, (mass (lam i) * normSq (c i) +
          2 * dot (c i) (moment (lam i) (v i)))) ≤ r2 := by
    have heq :
        (∑ i, ∑ j, lam i j * normSq (add (c i) (v i j))) =
        (∑ i, (mass (lam i) * normSq (c i) +
          2 * dot (c i) (moment (lam i) (v i)))) + 1 / 2 := by
      simp_rw [hexpand]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, htotal]
      ring
    rw [heq] at hweighted
    linarith
  have hsepSum :
      (∑ e, mu e * h e) ≤
      ∑ e, mu e * dot (n e) (sub (c (edgeEnd e)) (c (edgeStart e))) := by
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_left (hsep e) (hmu e)
  unfold dualValue
  apply summed_quadratic_lower r2 (1 / 2 + ∑ e, mu e * h e)
    (fun i => mass (lam i)) c (zVector v lam mu n) hw
  rw [energy_identity, force_identity]
  linarith

/-- Specialization of the algebraic certificate to genuinely contained squares. -/
theorem packing_dual_bound {S : Fin 3 → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R)
    (n : Fin 3 → Point) (lam : Fin 3 → Fin 4 → ℝ) (mu h : Fin 3 → ℝ)
    (hlam : ∀ i j, 0 ≤ lam i j)
    (hsum : (∑ i, ∑ j, lam i j) = 1)
    (hw : ∀ i, 0 < mass (lam i))
    (hmu : ∀ e, 0 ≤ mu e)
    (hsep : ∀ e, h e ≤ dot (n e)
      (sub (sub (S (edgeEnd e)).center o) (sub (S (edgeStart e)).center o))) :
    dualValue (fun i j => rotate (S i) (localVertex j)) lam mu h n ≤ R ^ 2 := by
  apply three_square_dual (R ^ 2) (fun i => sub (S i).center o)
    (fun i j => rotate (S i) (localVertex j)) n lam mu h
    hlam hsum hw hmu
  · intro i j
    rw [normSq_rotate, localVertex_normSq]
  · exact packing_vertex_bound hp
  · exact hsep

end ThreeUnitSquaresInCircle
