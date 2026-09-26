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
  ![s = .negative ∧ Side a u, s = .positive ∧ Side a u, Axial a u]
def kindOffset : Fin 3 → ℝ := ![-Real.pi/6,Real.pi/6,0]
def cycleKinds : Fin 6 → Fin 3 := ![0,1,2,0,1,2]
def cycleTurns : Fin 6 → Fin 4 := ![0,0,1,2,2,3]
def cycleTurnAngle : Fin 6 → ℝ := ![0,0,Real.pi/2,Real.pi,Real.pi,3*Real.pi/2]

lemma kind_unique {a u : ℝ} {s : TransverseSign} {i j : Fin 3}
    (hi : KindAt a u s i) (hj : KindAt a u s j) : i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [KindAt,Side,Axial]

lemma contact_kinds {a u A v : ℝ} {s t : TransverseSign}
    (hc : OrderedContact a u A v s t) :
    ∃ k : Fin 3, KindAt a u s k ∧ KindAt A v t (k+1) := by
  rcases hc with ⟨hs,ht,ha,hb⟩ | ⟨hs,ha,hb⟩ | ⟨ht,ha,hb⟩
  · exact ⟨0,⟨hs,ha⟩,⟨ht,hb⟩⟩
  · exact ⟨1,⟨hs,ha⟩,hb⟩
  · exact ⟨2,ha,⟨ht,hb⟩⟩

/-- An axial state is admissible. -/
lemma Axial.admissible {a u : ℝ} (h : Axial a u) : Admissible a u := by
  obtain ⟨rfl,h1,h2⟩ := h
  have := columnLimit_sq
  exact ⟨le_rfl,by linarith,h1,by dsimp [phi,targetSq]; nlinarith⟩

lemma kind_signed_label {a u : ℝ} {s : TransverseSign} {k : Fin 3} (hk : KindAt a u s k) :
    s.coe*label a u = kindOffset k := by
  fin_cases k
  · obtain ⟨rfl,rfl,rfl⟩ := hk
    norm_num [side_label,kindOffset,TransverseSign.coe,neg_div]
  · obtain ⟨rfl,rfl,rfl⟩ := hk
    norm_num [side_label,kindOffset,TransverseSign.coe]
  · change Axial a u at hk
    rw [hk.admissible.label_zero_iff.mpr hk.1]
    norm_num [kindOffset]

lemma rotate_next (j i : Fin 6) : Equiv.addRight j (next i) = next (Equiv.addRight j i) :=
  add_right_comm i 1 j

/-- A step `d` from each vertex of the hexagon to the next adds up to `i • d`. -/
lemma cycle_steps {A : Type*} [AddMonoid A] {f : Fin 6 → A} {d : A}
    (h : ∀ i, f (next i) = f i+d) (i : Fin 6) : f i = f 0+i.val • d := by
  have h1 : f 1 = f 0+d := h 0
  have h2 : f 2 = f 1+d := h 1
  have h3 : f 3 = f 2+d := h 2
  have h4 : f 4 = f 3+d := h 3
  have h5 : f 5 = f 4+d := h 4
  fin_cases i <;> simp [h1,h2,h3,h4,h5,succ_nsmul,add_assoc]

lemma kind_cycle_values (k : Fin 6 → Fin 3)
    (h0 : k 0 = 0) (h : ∀ i, k (next i) = k i+1) (i : Fin 6) : k i = cycleKinds i := by
  rw [cycle_steps h i,h0]
  fin_cases i <;> rfl

lemma cycle_turn_coe (i : Fin 6) :
    (cycleTurnAngle i : Direction) = quarterShift (cycleTurns i) := by
  fin_cases i <;> try rfl
  change ((3*Real.pi/2 : ℝ) : Direction) = ((-Real.pi/2 : ℝ) : Direction)
  rw [show 3*Real.pi/2 = -Real.pi/2+2*Real.pi by ring,Real.Angle.coe_add]
  simp

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
    (C : ∀ i, SquareChart (S i) o)
    (hm : ∀ i, (gap : Direction) = chartMarker (C (next i))-chartMarker (C i))
    (hc : ∀ i, OrderedContact (C i).a (C i).b (C (next i)).a (C (next i)).b
      (chartSign (C i)) (chartSign (C (next i)))) : Nonempty (ExteriorRing S o) := by
  choose k hk hn using (fun i => contact_kinds (hc i))
  have hstep (i : Fin 6) : k (next i) = k i+1 := kind_unique (hk (next i)) (hn i)
  obtain ⟨j,hj⟩ := (by decide : ∀ a : Fin 3, ∃ j : Fin 6, a+j.val • 1 = 0) (k 0)
  let σ := Equiv.addRight j
  have kval := kind_cycle_values (fun i => k (σ i))
    (by simpa [σ] using (cycle_steps hstep j).trans hj)
    (fun i => by rw [rotate_next]; exact hstep _)
  have hkind (i : Fin 6) : KindAt (C (σ i)).a (C (σ i)).b
      (chartSign (C (σ i))) (cycleKinds i) := kval i ▸ hk _
  have hgrid (i : Fin 6) :
      chartMarker (C (σ i)) = chartMarker (C (σ 0))+(((i.val : ℝ)*gap : ℝ) : Direction) := by
    rw [←nsmul_eq_mul,Real.Angle.coe_nsmul]
    exact cycle_steps (f := fun i => chartMarker (C (σ i)))
      (fun i => by rw [rotate_next]; exact eq_add_of_sub_eq' (hm _).symm) i
  let φ := (C (σ 0)).phase
  have hphase (i : Fin 6) : (C (σ i)).phase = φ+quarterShift (cycleTurns i) := by
    have hi := hgrid i
    rw [chartMarker_formula,chartMarker_formula,kind_signed_label (hkind i),
      kind_signed_label (hkind 0)] at hi
    rw [eq_sub_of_add_eq hi,←cycle_turn_coe,←cycle_phase_arithmetic,Real.Angle.coe_sub,
      Real.Angle.coe_sub]
    dsimp [φ,cycleKinds,kindOffset]
    rw [neg_div,Real.Angle.coe_neg]
    abel
  refine ⟨{ phase := φ, order := σ, top := (C (σ 2)).a, bottom := (C (σ 5)).a,
            top_bounds := (hkind 2).2, bottom_bounds := (hkind 5).2,
            represents := fun i => ?_ }⟩
  have hk := hkind i
  convert represents_quarter (cycleTurns i) (hphase i ▸ chart_represents (C (σ i))) using 1
  rw [←chartSign_coordinate]
  fin_cases i <;> simp [KindAt,cycleKinds] at hk <;>
    simp [cycleTurns,ringCenters,turnPoint,hk,TransverseSign.coe,neg_div]

/-- Six disjoint exterior squares at the optimal radius form the ring of the
optimal packing: two side columns, one square above and one below. -/
theorem six_exterior_ring (S : Fin 6 → UnitSquare) (o : Point)
    (hd : InteriorDisjoint S) (hext : ∀ i, ¬ openSquare (S i) o)
    (hphi : ∀ i, phi (alpha (S i) o) (beta (S i) o) ≤ targetSq) :
    Nonempty (ExteriorRing S o) := by
  choose C hsort using (fun i => sorted_square_chart (S i) o)
  have hadm (i : Fin 6) := chart_admissible (C i) (hsort i) (hext i) (hphi i)
  obtain ⟨φ,σ,hgrid⟩ := six_directions_hexagon (fun i => chartMarker (C i))
    (fun i j hij => marker_separation_closed (C i) (C j) (hadm i) (hadm j) (hd i j hij))
  have hm (i : Fin 6) : (gap : Direction) =
      chartMarker (C (σ (next i)))-chartMarker (C (σ i)) :=
    hexagon_successor hgrid i
  obtain ⟨W⟩ := ring_of_ordered_contacts (S := fun i => S (σ i)) (fun i => C (σ i)) hm
    fun i => ordered_chart_contact _ _ (hadm _) (hadm _) (hm i)
      (hd _ _ (fun he => (next_ne i) (σ.injective he).symm))
  exact ⟨{ W with order := W.order.trans σ, represents := W.represents }⟩

end Equality
end SquaresInCircles.Seven
