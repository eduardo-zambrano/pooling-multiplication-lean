import PoolingMultiplication.Counting

namespace PoolingMultiplication

/-- The ceiling example, written using natural-number division. -/
def diamond (a b : ℕ) : ℕ :=
  if a = 1 then b else ((2 * a - 1) * b + 1) / 2

theorem diamond_double_bounds {a b : ℕ} (ha : a ≠ 1) :
    (2 * a - 1) * b ≤ 2 * diamond a b ∧
      2 * diamond a b ≤ (2 * a - 1) * b + 1 := by
  simp only [diamond, if_neg ha]
  omega

theorem diamond_positive : Positive diamond := by
  intro a b ha hb
  by_cases h : a = 1
  · simpa [diamond, h] using hb
  · have hq : 0 < 2 * a - 1 := by omega
    have hm := Nat.mul_pos hq hb
    have hd := (diamond_double_bounds (b := b) h).1
    omega

theorem diamond_rightIdentity : RightIdentity diamond := by
  intro a ha
  simp only [diamond, mul_one]
  split_ifs <;> omega

theorem diamond_leftIdentity (b : ℕ) : diamond 1 b = b := by
  simp [diamond]

theorem diamond_rowStrict : RowStrict diamond := by
  intro a b c ha hb hbc
  by_cases h : a = 1
  · simpa [diamond, h] using hbc
  · have hq : 2 ≤ 2 * a - 1 := by omega
    have hm := Nat.mul_le_mul_left (2 * a - 1) (show b + 1 ≤ c by omega)
    have hdb := (diamond_double_bounds (b := b) h).2
    have hdc := (diamond_double_bounds (b := c) h).1
    nlinarith

theorem diamond_columnStrict {a c b : ℕ} (ha : 0 < a) (hac : a < c)
    (hb : 0 < b) : diamond a b < diamond c b := by
  have hc : c ≠ 1 := by omega
  have hdc := (diamond_double_bounds (b := b) hc).1
  by_cases h : a = 1
  · have hq : 3 ≤ 2 * c - 1 := by omega
    have hm := Nat.mul_le_mul_right b hq
    rw [show diamond a b = b by simp [diamond, h]]
    nlinarith
  · have hdb := (diamond_double_bounds (b := b) h).2
    have hq : (2 * a - 1) + 2 ≤ 2 * c - 1 := by omega
    have hm := Nat.mul_le_mul_right b hq
    nlinarith

theorem diamond_rowSub : RowSub diamond := by
  intro a b c ha hb hc
  by_cases h : a = 1
  · simp [diamond, h]
  · simp only [diamond, if_neg h, Nat.mul_add]
    omega

theorem diamond_rowSuper : RowSuper diamond := by
  intro a b c ha hb hc
  by_cases h : a = 1
  · simp [diamond, h]
  · simp only [diamond, if_neg h, Nat.mul_add]
    omega

theorem diamond_PS : PS diamond :=
  (ps_iff_rowSub diamond_positive diamond_rowStrict).2 diamond_rowSub

theorem diamond_PI : PI diamond :=
  (pi_iff_rowSuper diamond_positive diamond_rowStrict).2 diamond_rowSuper

theorem diamond_count_one (N : ℕ) : count diamond 1 N = N := by
  apply count_eq_of_threshold
  intro b hb
  simp [diamond]

theorem diamond_count {a : ℕ} (ha : 2 ≤ a) (N : ℕ) :
    count diamond a N = (2 * N) / (2 * a - 1) := by
  apply count_eq_of_threshold
  intro b hb
  have hq : 0 < 2 * a - 1 := by omega
  rw [Nat.le_div_iff_mul_le hq]
  simp only [diamond, if_neg (show a ≠ 1 by omega)]
  rw [Nat.mul_comm b (2 * a - 1)]
  omega

theorem diamond_not_comm : ¬ Comm diamond := by
  intro h
  have h24 := h 2 4 (by omega) (by omega)
  norm_num [diamond] at h24

theorem diamond_not_assoc : ¬ Assoc diamond := by
  intro h
  have h224 := h 2 2 4 (by omega) (by omega) (by omega)
  norm_num [diamond] at h224

end PoolingMultiplication
