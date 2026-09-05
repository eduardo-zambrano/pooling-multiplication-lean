import PoolingMultiplication.Counting
import PoolingMultiplication.Rigidity

/-! # The paper's main characterization theorem -/

namespace PoolingMultiplication

theorem rows_of_multiplication {op : Operation} (hmul : IsMultiplication op) :
    RowSub op ∧ RowSuper op := by
  constructor
  · intro a b c ha hb hc
    rw [hmul a (b + c) ha (by omega), hmul a b ha hb, hmul a c ha hc]
    simp [Nat.mul_add]
  · intro a b c ha hb hc
    rw [hmul a (b + c) ha (by omega), hmul a b ha hb, hmul a c ha hc]
    simp [Nat.mul_add]

/-- Theorem 2.1, with either (not necessarily both) row compatibility law. -/
theorem pooling_characterization {op : Operation} (hpos : Positive op)
    (hunit : RightIdentity op) (hstrict : RowStrict op)
    (hcompat : Comm op ∨ Assoc op) :
    (PS op ∧ PI op) ↔ IsMultiplication op := by
  constructor
  · rintro ⟨hps, hpi⟩
    have hsub := (ps_iff_rowSub hpos hstrict).mp hps
    have hsuper := (pi_iff_rowSuper hpos hstrict).mp hpi
    rcases hcompat with hcomm | hassoc
    · exact rigidity_of_comm hunit hsub hsuper hcomm
    · exact rigidity_of_assoc hpos hunit hsub hsuper hassoc
  · intro hmul
    have hrows := rows_of_multiplication hmul
    exact ⟨(ps_iff_rowSub hpos hstrict).mpr hrows.1,
      (pi_iff_rowSuper hpos hstrict).mpr hrows.2⟩

theorem pooling_characterization_comm {op : Operation} (hpos : Positive op)
    (hunit : RightIdentity op) (hstrict : RowStrict op) (hcomm : Comm op) :
    (PS op ∧ PI op) ↔ IsMultiplication op :=
  pooling_characterization hpos hunit hstrict (Or.inl hcomm)

theorem pooling_characterization_assoc {op : Operation} (hpos : Positive op)
    (hunit : RightIdentity op) (hstrict : RowStrict op) (hassoc : Assoc op) :
    (PS op ∧ PI op) ↔ IsMultiplication op :=
  pooling_characterization hpos hunit hstrict (Or.inr hassoc)

theorem comm_of_multiplication {op : Operation} (hmul : IsMultiplication op) :
    Comm op := by
  intro a b ha hb
  rw [hmul a b ha hb, hmul b a hb ha, Nat.mul_comm]

theorem assoc_of_multiplication {op : Operation} (hmul : IsMultiplication op) :
    Assoc op := by
  intro a b c ha hb hc
  rw [hmul a b ha hb, hmul b c hb hc,
    hmul (a * b) c (Nat.mul_pos ha hb) hc,
    hmul a (b * c) ha (Nat.mul_pos hb hc), Nat.mul_assoc]

theorem left_identity_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (b : ℕ) (hb : 0 < b) : op 1 b = b := by
  simpa using hmul 1 b (by omega) hb

theorem first_strict_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hc : 0 < c) :
    op a c < op b c := by
  rw [hmul a c ha hc, hmul b c (by omega) hc]
  exact Nat.mul_lt_mul_of_pos_right hab hc

theorem cancel_left_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : op a b = op a c) : b = c := by
  rw [hmul a b ha hb, hmul a c ha hc] at h
  exact Nat.eq_of_mul_eq_mul_left ha h

theorem cancel_right_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : op a c = op b c) : a = b := by
  rw [hmul a c ha hc, hmul b c hb hc] at h
  exact Nat.eq_of_mul_eq_mul_right hc h

end PoolingMultiplication
