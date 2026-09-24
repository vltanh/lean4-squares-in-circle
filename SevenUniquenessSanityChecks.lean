import SquaresInCircles.Seven.Uniqueness

/-! These regression proof scripts have not been compiled or executed. -/
noncomputable section
open SquaresInCircles SquaresInCircles.Seven

example (S : Fin 7 → UnitSquare) (o : Point) (hp : Packing S o radius) :
    SlidingNormalForm S o := uniqueness S o hp

example (S : Fin 7 → UnitSquare) (o : Point) :
    Packing S o radius ↔ SlidingNormalForm S o := packing_iff_sliding S o

example (S : Fin 7 → UnitSquare) (o : Point) (hp : Packing S o radius) :
    CongruentToSliding S o := rigid_uniqueness S o hp

example (c : Column) : Packing (slidingModel c) (0,0) radius := sliding_packing c
example (c : Column) : SlidingNormalForm (slidingModel c) (0,0) := slidingModel_normalForm c
example (c : Column) : ∑ i, c.slots i = 2*Real.sqrt 3-3 := c.sum_slots
example (c : Column) : columnSlotEquiv.symm (columnSlotEquiv c) = c :=
  columnSlotEquiv.symm_apply_apply c
example (g : SlotSimplex) : columnSlotEquiv (columnSlotEquiv.symm g) = g :=
  columnSlotEquiv.apply_symm_apply g
example (c : Column) : |c.middle| < 1/4 := column_middle_abs_lt_quarter c
example : (0 : ℝ) < 2*Real.sqrt 3-3 := sliding_slot_budget_pos

example : Equality.Side 1 (1/2) := ⟨rfl,rfl⟩
example : Equality.Axial 1 0 := ⟨rfl,by norm_num,one_le_columnLimit⟩
example : Equality.OrderedContact 1 (1/2) 1 (1/2) .negative .positive :=
  Or.inl ⟨rfl,rfl,⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
example {a : ℝ} (ha : 1/2 ≤ a ∧ a ≤ columnLimit) :
    Equality.OrderedContact 1 (1/2) a 0 .positive .negative :=
  Or.inr (Or.inl ⟨rfl,⟨rfl,rfl⟩,⟨rfl,ha.1,ha.2⟩⟩)

example {c s X Y : ℝ} (hu : c^2+s^2=1)
    (h0 : Equality.sectionOpen c s X Y 0 0)
    (hs : ∀ x y, Equality.sectionOpen c s X Y x y → |y| < 1 → |x| ≤ 1/2) :
    X=0 ∧ c*s=0 := by
  have hh := Equality.section_strip_rigidity hu h0 hs
  exact ⟨hh.1,hh.2.1⟩

example (c : Column) (S : Fin 7 → UnitSquare) (o : Point)
    (h : HasNormalForm S o (slidingCenters c)) : Packing S o radius :=
  SlidingNormalForm.packing ⟨c,h⟩
