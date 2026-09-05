import PoolingMultiplication.Basic

/-!
# Finite rigidity of a family of almost-additive rows

This module proves the algebraic core independently of the counting bridge.
The lower bound is written without truncated subtraction:
`a * b + 1 ≤ op a b + b`, equivalent to `(a - 1) * b + 1 ≤ op a b`
for positive `a`. Both compatibility arguments are finite.
-/

namespace PoolingMultiplication

theorem initial_bounds {op : Operation} (hunit : RightIdentity op)
    (hsub : RowSub op) (hsuper : RowSuper op)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    op a b ≤ a * b ∧ a * b + 1 ≤ op a b + b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.eq_zero_or_pos b with rfl | hb'
    · simp [hunit a ha]
    · have hi := ih hb'
      have h₁ := hsub a b 1 ha hb' (by omega)
      have h₂ := hsuper a b 1 ha hb' (by omega)
      rw [hunit a ha] at h₁ h₂
      constructor <;> nlinarith

theorem initial_lower_bound {op : Operation} (hunit : RightIdentity op)
    (hsub : RowSub op) (hsuper : RowSuper op)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a - 1) * b + 1 ≤ op a b := by
  have h := (initial_bounds hunit hsub hsuper a b ha hb).2
  have hpred : a - 1 + 1 = a := by omega
  nlinarith

theorem replicate {op : Operation} (hsub : RowSub op)
    (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    op a (k * b) ≤ k * op a b := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp
    · have hi := ih hk'
      have hs := hsub a (k * b) b ha (Nat.mul_pos hk' hb) hb
      simpa only [Nat.add_mul, Nat.one_mul] using
        (show op a ((k + 1) * b) ≤ (k + 1) * op a b by
          rw [Nat.add_mul, Nat.one_mul]
          nlinarith)

/-- Symmetry eliminates the one-unit row defect, without associativity. -/
theorem rigidity_of_comm {op : Operation} (hunit : RightIdentity op)
    (hsub : RowSub op) (hsuper : RowSuper op) (hcomm : Comm op) :
    IsMultiplication op := by
  intro a b ha hb
  have hup := (initial_bounds hunit hsub hsuper a b ha hb).1
  apply Nat.le_antisymm hup
  by_contra h
  have hgap : op a b + 1 ≤ a * b := by omega
  have hlo := (initial_bounds hunit hsub hsuper (a * b) a
    (Nat.mul_pos ha hb) ha).2
  rw [hcomm (a * b) a (Nat.mul_pos ha hb) ha] at hlo
  have hrep := replicate hsub a b a ha hb ha
  have hamp := Nat.mul_le_mul_left a hgap
  nlinarith

/-- Composition eliminates the one-unit row defect, without commutativity. -/
theorem rigidity_of_assoc {op : Operation} (hpos : Positive op)
    (hunit : RightIdentity op) (hsub : RowSub op) (hsuper : RowSuper op)
    (hassoc : Assoc op) : IsMultiplication op := by
  intro a b ha hb
  have hup := (initial_bounds hunit hsub hsuper a b ha hb).1
  apply Nat.le_antisymm hup
  by_contra h
  have hn : 0 < a * b := Nat.mul_pos ha hb
  have hgap : op a b + 1 ≤ a * b := by omega
  have h₁ := (initial_bounds hunit hsub hsuper (a * b) a hn ha).2
  have h₂ := (initial_bounds hunit hsub hsuper (op (a * b) a) b
    (hpos (a * b) a hn ha) hb).2
  rw [hassoc (a * b) a b hn ha hb] at h₂
  have h₃ := (initial_bounds hunit hsub hsuper (a * b) (op a b)
    hn (hpos a b ha hb)).1
  have hamp := Nat.mul_le_mul_right b h₁
  have hgapamp := Nat.mul_le_mul_left (a * b) hgap
  nlinarith

end PoolingMultiplication
