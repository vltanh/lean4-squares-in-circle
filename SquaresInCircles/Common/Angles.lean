import SquaresInCircles.Common.NormalForm
import SquaresInCircles.Common.ArcMetric
import Mathlib.Data.Fin.Tuple.Sort

/-! Small circular-order lemmas used only for the equality cases. -/
noncomputable section
open Set
namespace SquaresInCircles

lemma angle_ext {φ ψ : Direction} (hc : φ.cos=ψ.cos) (hs : φ.sin=ψ.sin) : φ=ψ := by
  have hcφ := congrArg Real.Angle.cos (Real.Angle.coe_toReal φ)
  have hcψ := congrArg Real.Angle.cos (Real.Angle.coe_toReal ψ)
  have hsφ := congrArg Real.Angle.sin (Real.Angle.coe_toReal φ)
  have hsψ := congrArg Real.Angle.sin (Real.Angle.coe_toReal ψ)
  simp only [Real.Angle.cos_coe,Real.Angle.sin_coe] at hcφ hcψ hsφ hsψ
  have h := Real.Angle.cos_sin_inj (hcφ.trans (hc.trans hcψ.symm))
    (hsφ.trans (hs.trans hsψ.symm))
  simpa only [Real.Angle.coe_toReal] using h

lemma antipodal_of_distance {φ ψ : Direction} (h : dist φ ψ=Real.pi) :
    ψ=φ+(Real.pi:Direction) := by
  have hc : (ψ-φ).cos= -1 := by rw [cos_sub_distance,h,Real.cos_pi]
  have hs : (ψ-φ).sin=0 := by nlinarith [Real.Angle.cos_sq_add_sin_sq (ψ-φ)]
  have he : ψ-φ=(Real.pi:Direction) := angle_ext
    (by simpa using hc) (by simpa using hs)
  exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)

def quarterShift : Fin 4 → Direction :=
  ![0,((Real.pi/2:ℝ):Direction),(Real.pi:Direction),((-Real.pi/2:ℝ):Direction)]
def turnPoint : Fin 4 → Point → Point :=
  ![(fun p => p),(fun p => (-p.2,p.1)),(fun p => (-p.1,-p.2)),(fun p => (p.2,-p.1))]

lemma represents_quarter {S : UnitSquare} {o : Point} {φ : Direction} {c : Point}
    (k : Fin 4) (h : Represents S o (φ+quarterShift k) c) :
    Represents S o φ (turnPoint k c) := by
  intro x y
  rw [pointInDirection_transition o φ (φ+quarterShift k)]
  rw [h]
  have he : φ+quarterShift k-φ=quarterShift k := by abel
  rw [he]
  fin_cases k <;>
    simp [quarterShift,turnPoint,openAxisSquare,neg_div,Real.Angle.cos_coe,Real.Angle.sin_coe] <;>
    constructor <;> rintro ⟨h1,h2⟩ <;>
    obtain ⟨h1a,h1b⟩ := abs_lt.mp h1 <;> obtain ⟨h2a,h2b⟩ := abs_lt.mp h2 <;>
    exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma sorted_three_grid {P x y z : ℝ}
    (hx : -P < x) (hz : z ≤ P)
    (hxabs : P/2 ≤ |x|) (hyabs : P/2 ≤ |y|)
    (hgap₁ : P/2 ≤ y-x) (hgap₂ : P/2 ≤ z-y) (hwrap : z-x ≤ 3*P/2) :
    x= -P/2 ∧ y=P/2 ∧ z=P := by
  have hy0 : 0 ≤ y := by
    by_contra hn
    rw [abs_of_neg (lt_of_not_ge hn)] at hyabs
    linarith
  rw [abs_of_nonneg hy0] at hyabs
  have hyEq : y=P/2 := by linarith
  have hzEq : z=P := by linarith
  have hx0 : x ≤ 0 := by linarith
  rw [abs_of_nonpos hx0] at hxabs
  exact ⟨by linarith,hyEq,hzEq⟩

/-- Four directions with mutual distances at least pi/2 are exactly a quarter-grid. -/
lemma four_directions_grid (θ : Fin 4 → Direction)
    (hsep : ∀ i j, i ≠ j → Real.pi/2 ≤ dist (θ i) (θ j)) :
    ∀ i, ∃ k : Fin 4, θ i=θ 0+quarterShift k := by
  let t : Fin 3 → ℝ := fun i => (θ i.succ-θ 0).toReal
  have ht (i : Fin 3) : -Real.pi < t i ∧ t i ≤ Real.pi ∧ Real.pi/2 ≤ |t i| := by
    refine ⟨(θ i.succ-θ 0).neg_pi_lt_toReal,(θ i.succ-θ 0).toReal_le_pi,?_⟩
    simpa only [t,direction_dist] using hsep i.succ 0 (Fin.succ_ne_zero i)
  have hpairs (i j : Fin 3) (hij : i ≠ j) :
      Real.pi/2 ≤ |t i-t j| ∧ |t i-t j| ≤ 3*Real.pi/2 := by
    have he : θ i.succ-θ j.succ=((t i-t j:ℝ):Direction) := by
      rw [Real.Angle.coe_sub]
      simp only [t,Real.Angle.coe_toReal]
      abel
    have h := hsep i.succ j.succ (by simpa using hij)
    have h₁ : dist (θ i.succ) (θ j.succ) ≤ |t i-t j| := by
      rw [dist_eq_norm,he]; exact direction_coe_norm_le _
    have h₂ : dist (θ i.succ) (θ j.succ) ≤ 2*Real.pi-|t i-t j| := by
      rw [dist_eq_norm,he]
      apply direction_norm_wrapped
      exact (abs_sub _ _).trans (by
        have hi := (θ i.succ-θ 0).abs_toReal_le_pi
        have hj := (θ j.succ-θ 0).abs_toReal_le_pi
        linarith)
    exact ⟨h.trans h₁,by linarith⟩
  obtain ⟨f,hf,h01,h12⟩ : ∃ f : Fin 3 → Fin 3, Function.Injective f ∧
      t (f 0) ≤ t (f 1) ∧ t (f 1) ≤ t (f 2) :=
    ⟨Tuple.sort t,(Tuple.sort t).injective,Tuple.monotone_sort t (by decide),
      Tuple.monotone_sort t (by decide)⟩
  have h01' := (hpairs (f 0) (f 1) (fun h => (by decide : (0:Fin 3) ≠ 1) (hf h))).1
  have h12' := (hpairs (f 1) (f 2) (fun h => (by decide : (1:Fin 3) ≠ 2) (hf h))).1
  have h02' := (hpairs (f 0) (f 2) (fun h => (by decide : (0:Fin 3) ≠ 2) (hf h))).2
  rw [abs_of_nonpos (sub_nonpos.mpr h01)] at h01'
  rw [abs_of_nonpos (sub_nonpos.mpr h12)] at h12'
  rw [abs_of_nonpos (sub_nonpos.mpr (h01.trans h12))] at h02'
  have hv := sorted_three_grid (ht (f 0)).1 (ht (f 2)).2.1
    (ht (f 0)).2.2 (ht (f 1)).2.2 (by linarith) (by linarith) (by linarith)
  have htgrid (i : Fin 3) : t i= -Real.pi/2 ∨ t i=Real.pi/2 ∨ t i=Real.pi := by
    obtain ⟨j,rfl⟩ := Finite.surjective_of_injective hf i
    fin_cases j
    · exact Or.inl hv.1
    · exact Or.inr (Or.inl hv.2.1)
    · exact Or.inr (Or.inr hv.2.2)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨0,by simp [quarterShift]⟩
  · have he : θ j.succ=θ 0+((t j:ℝ):Direction) := direction_offset _ _
    rcases htgrid j with h | h | h
    · exact ⟨3,by rw [he,h]; simp [quarterShift]⟩
    · exact ⟨1,by rw [he,h]; simp [quarterShift]⟩
    · exact ⟨2,by rw [he,h]; simp [quarterShift]⟩

lemma represents_cardinal {S : UnitSquare} {o : Point} {φ ψ : Direction} {c : Point}
    (h : Represents S o φ c) (k : Fin 4)
    (hc : (φ-ψ).cos=(quarterShift k).cos)
    (hs : (φ-ψ).sin=(quarterShift k).sin) :
    Represents S o ψ (turnPoint k c) := by
  have he : φ-ψ=quarterShift k := angle_ext hc hs
  have he' : φ=ψ+quarterShift k := by rw [← he]; abel
  rw [he'] at h
  exact represents_quarter k h

end SquaresInCircles
