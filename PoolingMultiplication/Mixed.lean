import PoolingMultiplication.Main

/-!
# Mixed-argument pooling

Subadditivity in the second argument and one-unit superadditivity in the
first argument force multiplication under two-sided normalization. This
threshold theorem assumes neither order nor an algebraic compatibility law.

The subsequent counting characterization separately assumes strict order
in both arguments, so the previously proved threshold/count equivalences
apply to both the operation and its transpose.
-/

namespace PoolingMultiplication

def transpose (op : Operation) : Operation := fun a b => op b a

def LeftIdentity (op : Operation) : Prop :=
  ∀ b, 0 < b → op 1 b = b

abbrev ColumnStrict (op : Operation) : Prop := RowStrict (transpose op)

abbrev ColumnSub (op : Operation) : Prop := RowSub (transpose op)

abbrev ColumnSuper (op : Operation) : Prop := RowSuper (transpose op)

theorem transpose_positive {op : Operation} (hp : Positive op) :
    Positive (transpose op) := by
  intro a b ha hb
  exact hp b a hb ha

theorem transpose_isMultiplication {op : Operation} (hmul : IsMultiplication op) :
    IsMultiplication (transpose op) := by
  intro a b ha hb
  change op b a = a * b
  rw [hmul b a hb ha, Nat.mul_comm]

private theorem row_sub_upper {op : Operation} (hunit : RightIdentity op)
    (hsub : RowSub op) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    op a b ≤ a * b := by
  have h := replicate hsub a 1 b ha (by omega) hb
  simpa [hunit a ha, Nat.mul_comm] using h

private theorem column_super_lower {op : Operation} (hunit : LeftIdentity op)
    (hsuper : ColumnSuper op) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a * b + 1 ≤ op a b + a := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha'
    · simp [hunit b hb]
    · have hi := ih ha'
      have hs := hsuper b a 1 hb ha' (by omega)
      change op a b + op 1 b ≤ op (a + 1) b + 1 at hs
      rw [hunit b hb] at hs
      nlinarith

/-- Mixed threshold rigidity: no positivity, monotonicity, commutativity,
or associativity hypothesis is needed beyond the displayed normalization
and functional inequalities on positive arguments. -/
theorem mixed_threshold_rigidity {op : Operation}
    (hright : RightIdentity op) (hleft : LeftIdentity op)
    (hsub : RowSub op) (hsuper : ColumnSuper op) :
    IsMultiplication op := by
  intro a b ha hb
  have hup := row_sub_upper hright hsub a b ha hb
  apply Nat.le_antisymm hup
  by_contra h
  have hgap : op a b + 1 ≤ a * b := by omega
  have hlo := column_super_lower hleft hsuper a (a * b) ha (Nat.mul_pos ha hb)
  have hrep := replicate hsub a b a ha hb ha
  have hamp := Nat.mul_le_mul_left a hgap
  nlinarith

/-- Genuine counting version of mixed pooling. `PS op` counts second
factors with the first factor fixed; `PI (transpose op)` counts first
factors with the second factor fixed. Both counting functions are the
actual set cardinalities from `Basic.lean`. -/
theorem mixed_pooling_characterization {op : Operation}
    (hpos : Positive op) (hright : RightIdentity op) (hleft : LeftIdentity op)
    (hrow : RowStrict op) (hcolumn : ColumnStrict op) :
    (PS op ∧ PI (transpose op)) ↔ IsMultiplication op := by
  have hpost := transpose_positive hpos
  constructor
  · rintro ⟨hps, hpi⟩
    exact mixed_threshold_rigidity hright hleft
      ((ps_iff_rowSub hpos hrow).mp hps)
      ((pi_iff_rowSuper hpost hcolumn).mp hpi)
  · intro hmul
    exact ⟨(ps_iff_rowSub hpos hrow).mpr (rows_of_multiplication hmul).1,
      (pi_iff_rowSuper hpost hcolumn).mpr
        (rows_of_multiplication (transpose_isMultiplication hmul)).2⟩

end PoolingMultiplication
