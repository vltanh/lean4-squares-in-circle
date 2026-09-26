import SquaresInCircles.Seven.Construction
import SquaresInCircles.Common.NormalForm

/-!
# The sliding normal form

`SlidingNormalForm S o` says that `S` has the normal form of
`slidingCenters c` for some column `c`; `CongruentToSliding` says the same
with an explicit isometry of the plane. Every sliding normal form is an
optimal packing.
-/
noncomputable section
namespace SquaresInCircles.Seven

/-- `S` has the normal form of some sliding packing. -/
def SlidingNormalForm (S : Fin 7 → UnitSquare) (o : Point) : Prop :=
  ∃ c : Column, HasNormalForm S o (slidingCenters c)

/-- `SlidingNormalForm` with an explicit isometry of the plane in place of the
frame. -/
def CongruentToSliding (S : Fin 7 → UnitSquare) (o : Point) : Prop :=
  ∃ (c : Column) (e : Point ≃ Point) (σ : Equiv.Perm (Fin 7)),
    e (0,0) = o ∧
    (∀ p q, normSq (sub (e p) (e q)) = normSq (sub p q)) ∧
    (∀ i p,
      (openSquare (S (σ i)) (e p) ↔ openAxisSquare (slidingCenters c i) p.1 p.2) ∧
      (closedSquare (S (σ i)) (e p) ↔ closedAxisSquare (slidingCenters c i) p.1 p.2))

lemma SlidingNormalForm.rigid {S : Fin 7 → UnitSquare} {o : Point}
    (h : SlidingNormalForm S o) : CongruentToSliding S o := by
  obtain ⟨c,hc⟩ := h
  obtain ⟨e,σ,he,hd,hm⟩ := hc.rigid_witness
  exact ⟨c,e,σ,he,hd,hm⟩

lemma slidingModel_open (c : Column) (i : Fin 7) (p : Point) :
    openSquare (slidingModel c i) p ↔ openAxisSquare (slidingCenters c i) p.1 p.2 := by
  simp [slidingModel,axisSquare,openSquare,openAxisSquare,localX,localY]

lemma slidingModel_closed (c : Column) (i : Fin 7) (p : Point) :
    closedSquare (slidingModel c i) p ↔ closedAxisSquare (slidingCenters c i) p.1 p.2 := by
  simp [slidingModel,axisSquare,closedSquare,closedAxisSquare,localX,localY]

/-- Every sliding normal form is an optimal packing. -/
theorem SlidingNormalForm.packing {S : Fin 7 → UnitSquare} {o : Point}
    (h : SlidingNormalForm S o) : Packing S o radius := by
  obtain ⟨c,φ,σ,hφ⟩ := h
  let e := frameEquiv o φ
  have hzero : e (0,0)=o := frameEquiv_zero o φ
  have hmodel := sliding_packing c
  refine ⟨radius_nonneg,?_,?_⟩
  · intro j p hp
    let i := σ.symm j
    let q := e.symm p
    have hi : σ i = j := σ.apply_symm_apply j
    have he : e q = p := e.apply_symm_apply p
    have hq : closedSquare (slidingModel c i) q := by
      apply (slidingModel_closed c i q).mpr
      apply ((hφ i q.1 q.2).2).mp
      simpa only [hi,←frameEquiv_apply,←he] using hp
    have hbound := hmodel.2.1 i q hq
    have hd := frameEquiv_distance o φ q (0,0)
    rw [show frameEquiv o φ q=p from he,frameEquiv_zero] at hd
    change normSq (sub p o) ≤ radius^2
    rw [hd]
    exact hbound
  · intro j k hjk p hp
    let i := σ.symm j
    let l := σ.symm k
    let q := e.symm p
    have hi : σ i=j := σ.apply_symm_apply j
    have hl : σ l=k := σ.apply_symm_apply k
    have he : e q=p := e.apply_symm_apply p
    have hil : i≠l := by
      intro h
      apply hjk
      rw [←hi,←hl,h]
    apply hmodel.2.2 i l hil q
    constructor
    · apply (slidingModel_open c i q).mpr
      apply ((hφ i q.1 q.2).1).mp
      simpa only [hi,←frameEquiv_apply,←he] using hp.1
    · apply (slidingModel_open c l q).mpr
      apply ((hφ l q.1 q.2).1).mp
      simpa only [hl,←frameEquiv_apply,←he] using hp.2

end SquaresInCircles.Seven
