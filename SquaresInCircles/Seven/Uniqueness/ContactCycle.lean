import SquaresInCircles.Seven.MarkerSeparation
import SquaresInCircles.Seven.CircleBudget
import SquaresInCircles.Common.Angles

/-!
# The ring of six squares

Round the regular hexagon of markers, consecutive squares are contacts, so
their kinds cycle through lower side, upper side and axial, twice. Read in one
frame, they are the two side columns and two axial squares at free heights.
-/
noncomputable section
namespace SquaresInCircles.Seven
namespace Equality

def KindAt (a u : ℝ) (s : TransverseSign) : Fin 3 → Prop :=
  ![s = .negative ∧ Side a u, s = .positive ∧ Side a u, u = 0]
def kindOffset : Fin 3 → ℝ := ![-Real.pi/6,Real.pi/6,0]
def cycleKinds : Fin 6 → Fin 3 := ![0,1,2,0,1,2]
def cycleTurns : Fin 6 → Fin 4 := ![0,0,1,2,2,3]
def cycleTurnAngle : Fin 6 → ℝ := ![0,0,Real.pi/2,Real.pi,Real.pi,3*Real.pi/2]

lemma kind_unique {a u : ℝ} {s : TransverseSign} {i j : Fin 3}
    (hi : KindAt a u s i) (hj : KindAt a u s j) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [KindAt,Side]

lemma contact_kinds {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact a u A v s t) :
    ∃ k : Fin 3, KindAt a u s k ∧ KindAt A v t (k+1) := by
  rcases hc with ⟨hs,ht,ha,hb⟩ | ⟨hs,ha,hb⟩ | ⟨ht,ha,hb⟩
  · exact ⟨0,⟨hs,ha⟩,⟨ht,hb⟩⟩
  · exact ⟨1,⟨hs,ha⟩,hb.1⟩
  · exact ⟨2,ha.1,⟨ht,hb⟩⟩

lemma kind_signed_label {a u : ℝ} {s : TransverseSign}
    (h : Admissible a u) {k : Fin 3} (hk : KindAt a u s k) :
    s.coe*label a u = kindOffset k := by
  fin_cases k
  · rcases hk with ⟨rfl,ha,hu⟩
    rw [ha,hu,side_label]
    norm_num [kindOffset,TransverseSign.coe,neg_div]
  · rcases hk with ⟨rfl,ha,hu⟩
    rw [ha,hu,side_label]
    norm_num [kindOffset,TransverseSign.coe]
  · change u = 0 at hk
    rw [h.label_zero_iff.mpr hk]
    norm_num [kindOffset]

def rotateOrder (j : Fin 6) : Equiv.Perm (Fin 6) where
  toFun i := i+j
  invFun i := i-j
  left_inv i := by simp
  right_inv i := by simp

lemma rotate_next (j i : Fin 6) : rotateOrder j (next i) = next (rotateOrder j i) := by
  dsimp [rotateOrder,next]
  abel

lemma kind_cycle_anchor (k : Fin 6 → Fin 3)
    (h : ∀ i, k (next i) = k i+1) : ∃ j, k j = 0 := by
  have h0 := h 0
  have h1 := h 1
  norm_num [next] at h0 h1
  by_cases hk0 : k 0 = 0
  · exact ⟨0,hk0⟩
  by_cases hk1 : k 0 = 1
  · refine ⟨2,?_⟩
    rw [h1,h0,hk1]
    norm_num
  · have hk2 : k 0 = 2 := by omega
    refine ⟨1,?_⟩
    rw [h0,hk2]
    norm_num

lemma kind_cycle_values (k : Fin 6 → Fin 3)
    (h0 : k 0 = 0) (h : ∀ i, k (next i) = k i+1) :
    ∀ i, k i = cycleKinds i := by
  have h1 : k 1 = 1 := by simpa [next,h0] using h 0
  have h2 : k 2 = 2 := by simpa [next,h1] using h 1
  have h3 : k 3 = 0 := by simpa [next,h2] using h 2
  have h4 : k 4 = 1 := by simpa [next,h3] using h 3
  have h5 : k 5 = 2 := by simpa [next,h4] using h 4
  intro i
  fin_cases i <;> simp [cycleKinds,h0,h1,h2,h3,h4,h5]

lemma coe_nat_gap (n : ℕ) : (((n : ℝ)*gap : ℝ) : Direction) = n • (gap : Direction) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Nat.cast_succ,add_mul,one_mul,Real.Angle.coe_add,ih,
        add_nsmul,one_nsmul]

lemma marker_steps (m : Fin 6 → Direction)
    (hm : ∀ i, (gap : Direction) = m (next i)-m i) :
    ∀ i, m i = m 0+(((i.val : ℝ)*gap : ℝ) : Direction) := by
  have hs (i : Fin 6) : m (next i) = m i+(gap : Direction) := by
    rw [hm i]
    abel
  have h1 := hs 0
  have h2 := hs 1
  have h3 := hs 2
  have h4 := hs 3
  have h5 := hs 4
  norm_num [next] at h1 h2 h3 h4 h5
  intro i
  rw [coe_nat_gap]
  fin_cases i <;> simp [h5,h4,h3,h2,h1] <;> abel

lemma cycle_turn_coe (i : Fin 6) :
    (cycleTurnAngle i : Direction) = quarterShift (cycleTurns i) := by
  have hlast : ((3*Real.pi/2 : ℝ) : Direction) = ((-Real.pi/2 : ℝ) : Direction) := by
    rw [show 3*Real.pi/2 = -Real.pi/2+2*Real.pi by ring,Real.Angle.coe_add]
    simp
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hlast

lemma cycle_phase_arithmetic (i : Fin 6) :
    (i.val : ℝ)*gap-kindOffset (cycleKinds i)-Real.pi/6 = cycleTurnAngle i := by
  fin_cases i <;> dsimp [gap,kindOffset,cycleKinds,cycleTurnAngle] <;> ring

end Equality

def ringCenters (top bottom : ℝ) : Fin 6 → Point :=
  ![(1,-1/2),(1,1/2),(0,top),(-1,1/2),(-1,-1/2),(0,-bottom)]

structure ExteriorRing (S : Fin 6 → UnitSquare) (o : Point) where
  phase : Direction
  order : Equiv.Perm (Fin 6)
  top : ℝ
  bottom : ℝ
  top_bounds : 1/2 ≤ top ∧ top ≤ columnLimit
  bottom_bounds : 1/2 ≤ bottom ∧ bottom ≤ columnLimit
  represents : ∀ i, Represents (S (order i)) o phase (ringCenters top bottom i)

namespace Equality

lemma ring_of_ordered_contacts {S : Fin 6 → UnitSquare} {o : Point}
    (C : ∀ i, SquareChart (S i) o) (hC : ∀ i, Admissible (C i).a (C i).b)
    (hm : ∀ i, (gap : Direction) = chartMarker (C (next i))-chartMarker (C i))
    (hc : ∀ i, OrderedContact (C i).a (C i).b (C (next i)).a (C (next i)).b
      (chartSign (C i)) (chartSign (C (next i)))) : Nonempty (ExteriorRing S o) := by
  classical
  choose k hk hn using (fun i => contact_kinds (hc i))
  have hstep (i : Fin 6) : k (next i) = k i+1 := kind_unique (hk (next i)) (hn i)
  obtain ⟨j,hj⟩ := kind_cycle_anchor k hstep
  let σ := rotateOrder j
  have ks (i : Fin 6) : k (σ (next i)) = k (σ i)+1 := by
    rw [rotate_next]
    exact hstep _
  have k0 : k (σ 0) = 0 := by simpa [σ,rotateOrder] using hj
  have kval := kind_cycle_values (fun i => k (σ i)) k0 ks
  have hkind (i : Fin 6) : KindAt (C (σ i)).a (C (σ i)).b
      (chartSign (C (σ i))) (cycleKinds i) := by
    rw [←kval i]
    exact hk _
  have hm' (i : Fin 6) : (gap : Direction) =
      chartMarker (C (σ (next i)))-chartMarker (C (σ i)) := by
    rw [rotate_next]
    exact hm _
  have hgrid := marker_steps (fun i => chartMarker (C (σ i))) hm'
  let φ := (C (σ 0)).phase
  have hoff (i : Fin 6) : (chartSign (C (σ i))).coe*
      label (C (σ i)).a (C (σ i)).b = kindOffset (cycleKinds i) :=
    kind_signed_label (hC _) (hkind i)
  have hphase (i : Fin 6) : (C (σ i)).phase = φ+quarterShift (cycleTurns i) := by
    have hi := hgrid i
    rw [chartMarker_formula,chartMarker_formula,hoff i,hoff 0] at hi
    have he := congrArg
      (fun z : Direction => z-((kindOffset (cycleKinds i) : ℝ) : Direction)) hi
    simp only [add_sub_cancel_right] at he
    have hreal := cycle_phase_arithmetic i
    have hcalc : (C (σ i)).phase =
        φ+(((i.val : ℝ)*gap-kindOffset (cycleKinds i)-Real.pi/6 : ℝ) : Direction) := by
      rw [he]
      simp only [Real.Angle.coe_sub]
      dsimp [φ,cycleKinds,kindOffset]
      rw [neg_div,Real.Angle.coe_neg]
      abel
    rw [hcalc,hreal,cycle_turn_coe]
  let top := (C (σ 2)).a
  let bottom := (C (σ 5)).a
  have ht : 1/2 ≤ top ∧ top ≤ columnLimit :=
    ⟨(hC _).2.2.1,(hC _).a_le_sqrt_three⟩
  have hb : 1/2 ≤ bottom ∧ bottom ≤ columnLimit :=
    ⟨(hC _).2.2.1,(hC _).a_le_sqrt_three⟩
  refine ⟨{ phase := φ, order := σ, top := top, bottom := bottom,
            top_bounds := ht, bottom_bounds := hb, represents := ?_ }⟩
  intro i
  have hr := chart_represents (C (σ i))
  rw [hphase i] at hr
  have hrot := represents_quarter (cycleTurns i) hr
  have he : turnPoint (cycleTurns i) ((C (σ i)).a,(C (σ i)).signedB) =
      ringCenters top bottom i := by
    rw [←chartSign_coordinate]
    fin_cases i
    · rcases hkind 0 with ⟨hs,ha,hu⟩
      simp [cycleTurns,ringCenters,turnPoint,hs,ha,hu,TransverseSign.coe,neg_div]
    · rcases hkind 1 with ⟨hs,ha,hu⟩
      simp [cycleTurns,ringCenters,turnPoint,hs,ha,hu,TransverseSign.coe]
    · have hu : (C (σ 2)).b = 0 := hkind 2
      simp [cycleTurns,ringCenters,turnPoint,hu,top]
    · rcases hkind 3 with ⟨hs,ha,hu⟩
      simp [cycleTurns,ringCenters,turnPoint,hs,ha,hu,TransverseSign.coe]
    · rcases hkind 4 with ⟨hs,ha,hu⟩
      simp [cycleTurns,ringCenters,turnPoint,hs,ha,hu,TransverseSign.coe,neg_div]
    · have hu : (C (σ 5)).b = 0 := hkind 5
      simp [cycleTurns,ringCenters,turnPoint,hu,bottom]
  simpa only [he] using hrot

/-- Six disjoint exterior squares at the optimal radius form the ring of the
optimal packing: two side columns, one square above and one below. -/
theorem six_exterior_ring (S : Fin 6 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hext : ∀ i, ¬ openSquare (S i) o)
    (hphi : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ targetSq) :
    Nonempty (ExteriorRing S o) := by
  classical
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hadm (i : Fin 6) := chart_admissible (C i) (hsort i) (hext i) (hphi i)
  have hsep (i j : Fin 6) (hij : i ≠ j) :
      gap ≤ dist (chartMarker (C i)) (chartMarker (C j)) :=
    marker_separation_closed (C i) (C j) (hadm i) (hadm j) (hd i j hij)
  obtain ⟨φ,σ,hgrid⟩ := six_directions_hexagon (fun i => chartMarker (C i)) hsep
  have hm (i : Fin 6) : (gap : Direction) =
      chartMarker (C (σ (next i)))-chartMarker (C (σ i)) :=
    hexagon_successor hgrid i
  have hc (i : Fin 6) : OrderedContact (C (σ i)).a (C (σ i)).b
      (C (σ (next i))).a (C (σ (next i))).b
      (chartSign (C (σ i))) (chartSign (C (σ (next i)))) :=
    ordered_chart_contact (C (σ i)) (C (σ (next i))) (hadm _) (hadm _) (hm i)
      (hd _ _ (fun he => (next_ne i) (σ.injective he).symm))
  obtain ⟨W⟩ := ring_of_ordered_contacts (S := fun i => S (σ i))
    (fun i => C (σ i)) (fun i => hadm _) hm hc
  exact ⟨{ phase := W.phase, order := W.order.trans σ,
           top := W.top, bottom := W.bottom, top_bounds := W.top_bounds,
           bottom_bounds := W.bottom_bounds, represents := W.represents }⟩

end Equality
end SquaresInCircles.Seven
