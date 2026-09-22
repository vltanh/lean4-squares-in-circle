import ThreeUnitSquaresInCircle.Unified.ThreeCaps

/-!
# The previously missing containing-square case

Three disjoint arc witnesses first bound the containing square's deficit.
A clipped exterior cap would compensate for that entire deficit. Otherwise
both exterior witnesses are full, nearly axial caps. Their midpoint distances
are controlled by the three-point circle perimeter inequality, and the explicit
Cartesian overlap witness contradicts ordinary interior-disjointness.

This module does not call the original certificate optimality theorem.
-/
noncomputable section
open Set
namespace ThreeUnitSquaresInCircle.Unified

/-- The containing alternative of the *strict contact-polygon* theorem. -/
theorem three_containing_impossible (S T U : UnitSquare) (o : Point)
    (hST : Disjoint {z | openSquare S z} {z | openSquare T z})
    (hSU : Disjoint {z | openSquare S z} {z | openSquare U z})
    (hTU : Disjoint {z | openSquare T z} {z | openSquare U z})
    (hS : P3Strict (alpha S o) (beta S o))
    (hT : P3Strict (alpha T o) (beta T o))
    (hU : P3Strict (alpha U o) (beta U o))
    (ho : openSquare S o) : False := by
  obtain ⟨C,hCsort⟩ := sorted_square_chart S o
  obtain ⟨D,hDsort⟩ := sorted_square_chart T o
  obtain ⟨E,hEsort⟩ := sorted_square_chart U o
  have hpC := C.p3Strict hS
  have hpD := D.p3Strict hT
  have hpE := E.p3Strict hU
  have hTo : ¬ openSquare T o := fun h => Set.disjoint_left.mp hST ho h
  have hUo : ¬ openSquare U o := fun h => Set.disjoint_left.mp hSU ho h
  have hDa := D.exterior hDsort hTo
  have hEa := E.exterior hEsort hUo
  have hinside := C.origin.mp ho
  obtain ⟨A,hA⟩ := three_containing_arc_formula C ho
  obtain ⟨B,hB⟩ := three_cap_arc_formula D hDa hpD
  obtain ⟨G,hG⟩ := three_cap_arc_formula E hEa hpE
  have hDdata := three_cap_data hDa D.nonneg.2 hpD
  have hEdata := three_cap_data hEa E.nonneg.2 hpE
  have hDlen : 2*Real.pi/3 < threeCapLength D.a D.b := hDdata.2.2.2.2.2
  have hElen : 2*Real.pi/3 < threeCapLength E.a E.b := hEdata.2.2.2.2.2
  have hbudget := triple_arc_budget A B G hST hSU hTU
  have hLsmall : threeContainingLength C.a C.b < 2*Real.pi/3 := by
    linarith

  let P : ℝ := (1/2-C.a)/auxThree
  let Q : ℝ := (1/2-C.b)/auxThree
  let L : ℝ := threeContainingLength C.a C.b
  let δ : ℝ := 2*Real.pi/3-L
  have hL : L=Real.pi/2+Real.arcsin P+Real.arcsin Q := rfl
  have hδ : δ=2*Real.pi/3-L := rfl
  have hA' : 2*A.halfWidth=L := hA
  obtain ⟨hP0,hPQ,hQ1,hcentral,hδpos0,hδsmall0⟩ :=
    three_deficit_bounds C.nonneg.1 C.nonneg.2 hCsort hinside.1 hinside.2 hpC hLsmall
  change 0 < P at hP0
  change P ≤ Q at hPQ
  change Q < 1 at hQ1
  change 1/2 < (16/13)*P+Q at hcentral
  change Real.pi/6-Real.arcsin P-Real.arcsin Q < 1/12 at hδsmall0
  have hδsmall : δ < 1/12 := by linarith
  have hQ : Q ∈ Icc (0:ℝ) 1 := ⟨hP0.le.trans hPQ,hQ1.le⟩

  have hgapD := three_gap_from_containing C D hCsort ho hDa hpD hST
  have hgapE := three_gap_from_containing C E hCsort ho hEa hpE hSU
  have hgapD' : P ≤ (D.a-1/2)/auxThree :=
    (div_le_div_iff_of_pos_right (by norm_num [auxThree])).mpr hgapD
  have hgapE' : P ≤ (E.a-1/2)/auxThree :=
    (div_le_div_iff_of_pos_right (by norm_num [auxThree])).mpr hgapE
  have hbudD : threeCapLength D.a D.b+L < 4*Real.pi/3 := by linarith
  have hbudE : threeCapLength E.a E.b+L < 4*Real.pi/3 := by linarith
  obtain ⟨hDfull,hDb,hDamax⟩ := three_cap_reduction hDa D.nonneg.2 hpD
    hP0.le hQ hcentral hgapD' hL hδ hδsmall hbudD
  obtain ⟨hEfull,hEb,hEamax⟩ := three_cap_reduction hEa E.nonneg.2 hpE
    hP0.le hQ hcentral hgapE' hL hδ hδsmall hbudE

  let Bfull := threeFullCap D hDa hpD hDfull
  let Gfull := threeFullCap E hEa hpE hEfull
  have hdist := A.third_distance_bounds Bfull Gfull hST hSU hTU
  change
    threeCapA D.a+threeCapA E.a ≤ dist D.phase E.phase ∧
    dist D.phase E.phase ≤ 2*Real.pi-2*A.halfWidth-threeCapA D.a-threeCapA E.a
    at hdist
  have hlo : 2*Real.pi/3 ≤ dist D.phase E.phase := by
    linarith [hDdata.2.2.2.1,hEdata.2.2.2.1,hdist.1]
  have hhi : dist D.phase E.phase < 2*Real.pi/3+1/12 := by
    linarith [hDdata.2.2.2.1,hEdata.2.2.2.1,hdist.2]
  obtain ⟨z,hzT,hzU⟩ := near_axis_square_overlap D E
    ⟨hDa,hDamax⟩ hDb ⟨hEa,hEamax⟩ hEb hlo hhi
  exact Set.disjoint_left.mp hTU hzT hzU

/-- No origin-containing branch is assumed or omitted: all three labels are handled. -/
theorem three_polygon_strict_impossible (S : Fin 3 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S)
    (hp : ∀ i, P3Strict (alpha (S i) o) (beta (S i) o)) : False := by
  have hpair (i j : Fin 3) (hij : i ≠ j) :
      Disjoint {z | openSquare (S i) z} {z | openSquare (S j) z} := by
    rw [Set.disjoint_left]
    exact fun z hz hz' => hd i j hij z ⟨hz,hz'⟩
  obtain ⟨i,hi⟩ := three_exterior_reduction S o hd hp
  fin_cases i
  · exact three_containing_impossible (S 0) (S 1) (S 2) o
      (hpair 0 1 (by decide)) (hpair 0 2 (by decide)) (hpair 1 2 (by decide))
      (hp 0) (hp 1) (hp 2) hi
  · exact three_containing_impossible (S 1) (S 0) (S 2) o
      (hpair 1 0 (by decide)) (hpair 1 2 (by decide)) (hpair 0 2 (by decide))
      (hp 1) (hp 0) (hp 2) hi
  · exact three_containing_impossible (S 2) (S 0) (S 1) o
      (hpair 2 0 (by decide)) (hpair 2 1 (by decide)) (hpair 0 1 (by decide))
      (hp 2) (hp 0) (hp 1) hi

end ThreeUnitSquaresInCircle.Unified
