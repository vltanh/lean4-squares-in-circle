import SquaresInCircles.Common.ArcMetric
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Seven.Labels
import Mathlib.Data.Finset.Sort

/-! Six directions with pairwise distance at least pi/3 form a regular hexagon.
This uncompiled draft sorts forward angular representatives and retains all
six nonnegative gap remainders. -/
noncomputable section
open Set
namespace SquaresInCircles.Seven.Equality

def forwardAngle (θ : Direction) : ℝ :=
  if θ.toReal<0 then θ.toReal+2*Real.pi else θ.toReal

lemma forwardAngle_range (θ : Direction) : 0≤forwardAngle θ ∧ forwardAngle θ<2*Real.pi := by
  have h := abs_le.mp θ.abs_toReal_le_pi
  unfold forwardAngle
  split_ifs <;> constructor <;> linarith [Real.pi_pos]

lemma coe_forwardAngle (θ : Direction) : (forwardAngle θ : Direction)=θ := by
  unfold forwardAngle
  split_ifs <;> simp [Real.Angle.coe_add,Real.Angle.coe_toReal]

lemma forwardAngle_zero : forwardAngle (0 : Direction)=0 := by simp [forwardAngle]

private lemma sorted_angles (c : Fin 6 → Direction)
    (hinj : Function.Injective c) :
    ∃ (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ℝ), StrictMono x ∧
      (∀ i,0≤x i ∧ x i<2*Real.pi) ∧ x 0=0 ∧
      (∀ i,c (σ i)=c 0+(x i : Direction)) := by
  classical
  let f : Fin 6 → ℝ := fun i => forwardAngle (c i-c 0)
  have hf : Function.Injective f := by
    intro i j hij
    have he := congrArg (fun r : ℝ => (r : Direction)) hij
    change (forwardAngle (c i-c 0) : Direction)=(forwardAngle (c j-c 0) : Direction) at he
    rw [coe_forwardAngle,coe_forwardAngle] at he
    exact hinj (sub_right_cancel he)
  let A : Finset ℝ := Finset.univ.image f
  have hcard : A.card=6 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  let toA : Fin 6 → A := fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have htoA : Function.Bijective toA := by
    constructor
    · intro i j hij
      exact hf (congrArg Subtype.val hij)
    · intro y
      obtain ⟨i,hi,he⟩ := Finset.mem_image.mp y.property
      exact ⟨i,Subtype.ext he⟩
  let e : Fin 6 ≃ A := Equiv.ofBijective toA htoA
  let o : Fin 6 ≃o A := A.orderIsoOfFin hcard
  let σ : Equiv.Perm (Fin 6) := o.toEquiv.trans e.symm
  let x : Fin 6 → ℝ := A.orderEmbOfFin hcard
  have hx : ∀ i,x i=f (σ i) := by
    intro i
    have he := congrArg Subtype.val (e.apply_symm_apply (o i))
    exact he.symm
  have hmono : StrictMono x := (A.orderEmbOfFin hcard).strictMono
  have hr (i : Fin 6) : 0≤x i ∧ x i<2*Real.pi := by
    rw [hx]
    exact forwardAngle_range _
  have hz : x 0=0 := by
    let j := σ.symm 0
    have hj : x j=0 := by
      rw [hx]
      simp [j,f]
    have hle : x 0≤x j := hmono.monotone (Fin.zero_le _)
    rw [hj] at hle
    exact le_antisymm hle (hr 0).1
  refine ⟨σ,x,hmono,hr,hz,?_⟩
  intro i
  rw [hx]
  change c (σ i)=c 0+(forwardAngle (c (σ i)-c 0) : Direction)
  rw [coe_forwardAngle]
  abel

theorem six_markers_hexagon (c : Fin 6 → Direction)
    (hsep : Pairwise (fun i j => gap≤dist (c i) (c j))) :
    ∃ (φ : Direction) (σ : Equiv.Perm (Fin 6)),
      ∀ i,c (σ i)=φ+(((i.val : ℝ)*gap) : Direction) := by
  classical
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hn
    have h := hsep hn
    rw [hij,dist_self] at h
    dsimp [gap] at h
    linarith [Real.pi_pos]
  obtain ⟨σ,x,hmono,hr,hzero,hrep⟩ := sorted_angles c hinj
  have hadj (i : Fin 5) : gap≤x i.succ-x i.castSucc := by
    have hij : σ i.castSucc≠σ i.succ := by
      intro he
      have hh := σ.injective he
      have hv := congrArg Fin.val hh
      simp only [Fin.val_castSucc,Fin.val_succ] at hv
      omega
    have h := hsep hij
    have he : c (σ i.succ)-c (σ i.castSucc)=
        ((x i.succ-x i.castSucc : ℝ) : Direction) := by
      rw [hrep,hrep,Real.Angle.coe_sub]
      abel
    have hnon : 0≤x i.succ-x i.castSucc :=
      sub_nonneg.mpr (hmono.monotone (by simp; omega))
    have hd : dist (c (σ i.castSucc)) (c (σ i.succ))≤x i.succ-x i.castSucc := by
      rw [dist_comm,dist_eq_norm,he]
      simpa only [abs_of_nonneg hnon] using direction_coe_norm_le (x i.succ-x i.castSucc)
    exact h.trans hd
  have hwrap : gap≤2*Real.pi-x 5+x 0 := by
    have hij : σ (5 : Fin 6)≠σ 0 := by
      intro he
      have hh := σ.injective he
      norm_num at hh
    have h := hsep hij
    have he : c (σ 5)-c (σ 0)=((x 5-x 0 : ℝ):Direction) := by
      rw [hrep,hrep,Real.Angle.coe_sub]
      abel
    have hnon : 0≤x 5-x 0 := sub_nonneg.mpr (hmono.monotone (by decide))
    have hbound : |x 5-x 0|≤2*Real.pi := by
      rw [abs_of_nonneg hnon]
      linarith [(hr 5).2,(hr 0).1]
    have hd := direction_norm_wrapped hbound
    rw [abs_of_nonneg hnon] at hd
    rw [dist_eq_norm,he] at h
    linarith
  have h0 := hadj 0
  have h1 := hadj 1
  have h2 := hadj 2
  have h3 := hadj 3
  have h4 := hadj 4
  norm_num only [Fin.succ,Fin.castSucc] at h0 h1 h2 h3 h4
  have hx (i : Fin 6) : x i=(i.val : ℝ)*gap := by
    fin_cases i <;> norm_num at * <;> dsimp [gap] at * <;> linarith
  refine ⟨c 0,σ,?_⟩
  intro i
  rw [hrep,hx]

theorem seven_markers_impossible (c : Fin 7 → Direction)
    (hsep : Pairwise (fun i j => gap≤dist (c i) (c j))) : False := by
  let r : ℝ := 13*Real.pi/84
  have hr : 0<r := by dsimp [r]; positivity
  have hballs : Pairwise (fun i j => Disjoint
      (Metric.closedBall (c i) r) (Metric.closedBall (c j) r)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hi hj
    have ht := dist_triangle (c i) z (c j)
    have hi' : dist (c i) z≤r := by simpa only [dist_comm] using hi
    have hj' : dist z (c j)≤r := hj
    have hs := hsep hij
    dsimp [r,gap] at *
    linarith [Real.pi_pos]
  have hb := closed_arc_budget c (fun _ => r)
    (fun _ => ⟨hr.le,by dsimp [r]; linarith [Real.pi_pos]⟩) hballs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  dsimp [r] at hb
  nlinarith [Real.pi_pos]

end SquaresInCircles.Seven.Equality
