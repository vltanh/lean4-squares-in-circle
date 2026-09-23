import SquaresInCircles.Common.Constructions

/-!
# The T construction and its exact enclosing radius

These proofs concern a specific arrangement and its best enclosing disk.
They do NOT assert that every three-square arrangement is no better.
-/

noncomputable section
namespace SquaresInCircles

/-- The optimal radius for three unit squares: the distance from the disk centre
to the corners of the T. -/
def Three.radius : ℝ := 5 * Real.sqrt 17 / 16

lemma Three.radius_nonneg : 0 ≤ Three.radius := by
  unfold Three.radius
  positivity

lemma Three.radius_sq : Three.radius ^ 2 = 425 / 256 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
  unfold Three.radius
  nlinarith

def tSquares : Fin 3 → UnitSquare :=
  ![axisSquare (-1) (-1), axisSquare 0 (-1), axisSquare (-1 / 2) 0]

def tCenter : Point := (0, -3 / 16)

lemma lower_strip_fits (p : Point)
    (hx0 : -1 ≤ p.1) (hx1 : p.1 ≤ 1)
    (hy0 : -1 ≤ p.2) (hy1 : p.2 ≤ 0) :
    inDisk tCenter Three.radius p := by
  have hx := sq_le_of_interval hx0 hx1
  have hy : (p.2 + 3 / 16) ^ 2 ≤ (13 / 16 : ℝ) ^ 2 :=
    sq_le_of_interval (by linarith) (by linarith)
  unfold inDisk
  rw [Three.radius_sq]
  dsimp [normSq, sub, tCenter]
  nlinarith

lemma upper_square_fits (p : Point)
    (hx0 : -(1 / 2 : ℝ) ≤ p.1) (hx1 : p.1 ≤ 1 / 2)
    (hy0 : 0 ≤ p.2) (hy1 : p.2 ≤ 1) :
    inDisk tCenter Three.radius p := by
  have hx := sq_le_of_interval hx0 hx1
  have hy : (p.2 + 3 / 16) ^ 2 ≤ (19 / 16 : ℝ) ^ 2 :=
    sq_le_of_interval (by linarith) (by linarith)
  unfold inDisk
  rw [Three.radius_sq]
  dsimp [normSq, sub, tCenter]
  nlinarith

lemma tSquares_contained (i : Fin 3) (p : Point)
    (h : closedSquare (tSquares i) p) : inDisk tCenter Three.radius p := by
  fin_cases i
  · change closedSquare (axisSquare (-1) (-1)) p at h
    rcases (closed_axisSquare_iff _ _ _).mp h with ⟨hx0, hx1, hy0, hy1⟩
    exact lower_strip_fits p hx0 (by linarith) hy0 (by linarith)
  · change closedSquare (axisSquare 0 (-1)) p at h
    rcases (closed_axisSquare_iff _ _ _).mp h with ⟨hx0, hx1, hy0, hy1⟩
    exact lower_strip_fits p (by linarith) (by linarith) hy0 (by linarith)
  · change closedSquare (axisSquare (-1 / 2) 0) p at h
    rcases (closed_axisSquare_iff _ _ _).mp h with ⟨hx0, hx1, hy0, hy1⟩
    exact upper_square_fits p (by linarith) (by linarith) hy0 (by linarith)

lemma axis_disjoint_horizontal {x y x' y' : ℝ} (h : x + 1 ≤ x') (p : Point) :
    ¬ (openSquare (axisSquare x y) p ∧ openSquare (axisSquare x' y') p) := by
  rintro ⟨h0, h1⟩
  rcases (open_axisSquare_iff _ _ _).mp h0 with ⟨_, hx, _, _⟩
  rcases (open_axisSquare_iff _ _ _).mp h1 with ⟨hx', _, _, _⟩
  linarith

lemma axis_disjoint_vertical {x y x' y' : ℝ} (h : y + 1 ≤ y') (p : Point) :
    ¬ (openSquare (axisSquare x y) p ∧ openSquare (axisSquare x' y') p) := by
  rintro ⟨h0, h1⟩
  rcases (open_axisSquare_iff _ _ _).mp h0 with ⟨_, _, _, hy⟩
  rcases (open_axisSquare_iff _ _ _).mp h1 with ⟨_, _, hy', _⟩
  linarith

lemma tSquares_disjoint (i j : Fin 3) (hij : i ≠ j) (p : Point) :
    ¬ (openSquare (tSquares i) p ∧ openSquare (tSquares j) p) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact axis_disjoint_horizontal (by norm_num) p
  · exact axis_disjoint_vertical (by norm_num) p
  · intro h
    exact axis_disjoint_horizontal (by norm_num) p ⟨h.2, h.1⟩
  · exact (hij rfl).elim
  · exact axis_disjoint_vertical (by norm_num) p
  · intro h
    exact axis_disjoint_vertical (by norm_num) p ⟨h.2, h.1⟩
  · intro h
    exact axis_disjoint_vertical (by norm_num) p ⟨h.2, h.1⟩
  · exact (hij rfl).elim

/-- An unconditional construction at the optimal radius. -/
theorem tSquares_packing : Packing tSquares tCenter Three.radius := by
  exact ⟨Three.radius_nonneg, tSquares_contained, tSquares_disjoint⟩

theorem Three.attainment :
    ∃ (S : Fin 3 → UnitSquare) (o : Point), Packing S o Three.radius :=
  ⟨tSquares, tCenter, tSquares_packing⟩

/-- The T in the frame of its disk centre `tCenter`. -/
def Three.centers : Fin 3 → Point := ![(-1/2,-5/16),(1/2,-5/16),(0,11/16)]

end SquaresInCircles
