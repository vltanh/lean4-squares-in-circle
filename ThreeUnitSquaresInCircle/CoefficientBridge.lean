import ThreeUnitSquaresInCircle.BranchCover
import ThreeUnitSquaresInCircle.Dual

/-! real geometry / rational coefficient identity. Compiles against Lean 4.34.0 / mathlib v4.34.0. -/
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
open scoped BigOperators
namespace ThreeUnitSquaresInCircle.Cert
open RatData

def theta (x : Point) : Fin 3 → ℝ := ![0, Real.pi*x.1, Real.pi*x.2]

def rotation (t : ℝ) (p : Point) : Point :=
  (Real.cos t*p.1-Real.sin t*p.2, Real.sin t*p.1+Real.cos t*p.2)

def castPoint (p : RPoint) : Point := (p.1,p.2)

def angularSquares (c : Fin 3 → Point) (x : Point) : Fin 3 → UnitSquare :=
  fun i => {
    center := c i
    cosine := Real.cos (theta x i)
    sine := Real.sin (theta x i)
    unit := by nlinarith [Real.sin_sq_add_cos_sq (theta x i)] }

def vertices (x : Point) (i : Fin 3) (j : Fin 4) : Point :=
  rotation (theta x i) (localVertex j)

def normal (x : Point) (k : Fin 3 → Fin 4) (s : Fin 3 → Fin 3) (e : Fin 3) : Point :=
  rotation (theta x (s e)) (castPoint (dirs (k e)))

def halfWidth (t : ℝ) : ℝ := (1+Real.cos t+Real.sin t)/2

def widths (x : Point) (e : Fin 3) : ℝ := halfWidth (arguments x e)

def lamReal (c : Certificate) (i : Fin 3) (j : Fin 4) : ℝ := c.lam i j

def muReal (c : Certificate) (e : Fin 3) : ℝ := c.mu e

/-- All 53 symbolic identities are real equalities, not checks of a Python output. -/
theorem coefficient_identity (i : Fin 53) (x : Point) :
    dualValue (vertices x) (lamReal (table i)) (muReal (table i))
      (widths x) (normal x (table i).k (table i).source) = polynomial (table i) x := by
  have hA := Real.sin_sq_add_cos_sq (Real.pi*x.1)
  have hB := Real.sin_sq_add_cos_sq (Real.pi*x.2)
  fin_cases i
  all_goals
    norm_num [table, cert000, cert001, cert002, cert003, cert004, cert005, cert006, cert007, cert008, cert009, cert010, cert011, cert012, cert013, cert014, cert015, cert016, cert017, cert018, cert019, cert020, cert021, cert022, cert023, cert024, cert025, cert026, cert027, cert028, cert029, cert030, cert031, cert032, cert033, cert034, cert035, cert036, cert037, cert038, cert039, cert040, cert041, cert042, cert043, cert044, cert045, cert046, cert047, cert048, cert049, cert050, cert051, cert052, dualValue, zVector, mass, moment,
      force, edgeStart, edgeEnd, vertices, normal, widths, halfWidth,
      lamReal, muReal, theta, arguments, rotation, castPoint, dirs, localVertex,
      normSq, dot, add, sub, scale, polynomial, A, B,
      Fin.sum_univ_succ, Real.sin_sub, Real.cos_sub]
    nlinarith [hA,hB]

/-- Rational admissibility transfers to the real primal-dual inequality. -/
theorem table_dual_bound (i : Fin 53) (x : Point) (c : Fin 3 → Point) (R : ℝ)
    (hp : Packing (angularSquares c x) (0,0) R)
    (hsep : ∀ e, widths x e ≤ dot
      (normal x (table i).k (table i).source e)
      (sub (c (edgeEnd e)) (c (edgeStart e)))) :
    polynomial (table i) x ≤ R^2 := by
  rcases table_checked i with
    ⟨hk0,hs,hlam,hsum,hw,hmu,hcoeff,hcurv0,hcurv1,hcurv2,hcorners⟩
  rw [← coefficient_identity i x]
  apply three_square_dual (R^2) c (vertices x)
    (normal x (table i).k (table i).source)
    (lamReal (table i)) (muReal (table i)) (widths x)
  · intro i j
    change (0:ℝ) ≤ ((table _).lam i j : ℝ)
    exact_mod_cast hlam i j
  · change (∑ j, ∑ k, ((table i).lam j k : ℝ)) = 1
    exact_mod_cast hsum
  · intro j
    change (0:ℝ) < ∑ k, ((table i).lam j k : ℝ)
    have h : (0:ℚ) < ∑ k, (table i).lam j k := hw j
    exact_mod_cast h
  · intro e
    change (0:ℝ) ≤ ((table i).mu e : ℝ)
    exact_mod_cast hmu e
  · intro j k
    change normSq (rotate (angularSquares c x j) (localVertex k)) = 1/2
    rw [normSq_rotate,localVertex_normSq]
  · intro j k
    simpa [vertices, rotation, angularSquares, sub, add, rotate] using
      packing_vertex_bound hp j k
  · exact hsep

end ThreeUnitSquaresInCircle.Cert
