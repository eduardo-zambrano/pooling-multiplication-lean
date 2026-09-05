import PoolingMultiplication.Counting

namespace PoolingMultiplication

/-- Multiplication with a missing normalization. -/
def doubleMul (a b : ℕ) : ℕ := 2 * a * b

theorem doubleMul_positive : Positive doubleMul := by
  intro a b ha hb
  exact Nat.mul_pos (Nat.mul_pos (by omega) ha) hb

theorem doubleMul_rowStrict : RowStrict doubleMul := by
  intro a b c ha hb hbc
  exact Nat.mul_lt_mul_of_pos_left hbc (Nat.mul_pos (by omega) ha)

theorem doubleMul_comm : Comm doubleMul := by
  intro a b ha hb
  unfold doubleMul
  ring

theorem doubleMul_columnStrict {a c b : ℕ} (_ha : 0 < a) (hac : a < c)
    (hb : 0 < b) : doubleMul a b < doubleMul c b := by
  unfold doubleMul
  nlinarith

theorem doubleMul_assoc : Assoc doubleMul := by
  intro a b c ha hb hc
  unfold doubleMul
  ring

theorem doubleMul_rowSub : RowSub doubleMul := by
  intro a b c ha hb hc
  simp [doubleMul, Nat.mul_add]

theorem doubleMul_rowSuper : RowSuper doubleMul := by
  intro a b c ha hb hc
  simp [doubleMul, Nat.mul_add]

theorem doubleMul_PS : PS doubleMul :=
  (ps_iff_rowSub doubleMul_positive doubleMul_rowStrict).2 doubleMul_rowSub

theorem doubleMul_PI : PI doubleMul :=
  (pi_iff_rowSuper doubleMul_positive doubleMul_rowStrict).2 doubleMul_rowSuper

theorem doubleMul_count {a : ℕ} (ha : 0 < a) (N : ℕ) :
    count doubleMul a N = N / (2 * a) := by
  apply count_eq_of_threshold
  intro b hb
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos (by omega) ha)]
  simp [doubleMul, Nat.mul_comm]

theorem doubleMul_not_rightIdentity : ¬ RightIdentity doubleMul := by
  intro h
  have h1 := h 1 (by omega)
  norm_num [doubleMul] at h1

/-- Symmetric difference transported from natural numbers to positive ranks. -/
def xorOp (a b : ℕ) : ℕ := 1 + ((a - 1) ^^^ (b - 1))

theorem xorOp_positive : Positive xorOp := by
  intro a b ha hb
  unfold xorOp
  omega

theorem xorOp_rightIdentity : RightIdentity xorOp := by
  intro a ha
  simp only [xorOp, Nat.sub_self, Nat.xor_zero]
  omega

theorem xorOp_leftIdentity {b : ℕ} (hb : 0 < b) : xorOp 1 b = b := by
  simp only [xorOp, Nat.sub_self, Nat.zero_xor]
  omega

theorem xorOp_comm : Comm xorOp := by
  intro a b ha hb
  simp [xorOp, Nat.xor_comm]

theorem xorOp_assoc : Assoc xorOp := by
  intro a b c ha hb hc
  simp [xorOp, Nat.xor_assoc]

theorem xorOp_involution (a : ℕ) {b : ℕ} (hb : 0 < b) :
    xorOp a (xorOp a b) = b := by
  simp only [xorOp, Nat.add_sub_cancel_left, Nat.xor_cancel_left]
  omega

theorem xorOp_not_rowStrict : ¬ RowStrict xorOp := by
  intro h
  have h212 := h 2 1 2 (by omega) (by omega) (by omega)
  norm_num [xorOp] at h212

theorem xorOp_feasible_image (a N : ℕ) :
    {b : ℕ | 0 < b ∧ xorOp a b ≤ N} = xorOp a '' Set.Icc 1 N := by
  ext b
  constructor
  · rintro ⟨hb, hN⟩
    refine ⟨xorOp a b, ?_, xorOp_involution a hb⟩
    constructor
    · unfold xorOp
      omega
    · exact hN
  · rintro ⟨j, hj, rfl⟩
    constructor
    · unfold xorOp
      omega
    · rw [xorOp_involution a (by have := hj.1; omega)]
      exact hj.2

theorem xorOp_count (a N : ℕ) : count xorOp a N = N := by
  unfold count
  rw [xorOp_feasible_image]
  have hinj : Set.InjOn (xorOp a) (Set.Icc 1 N) := by
    intro b hb c hc hbc
    have h := congrArg (xorOp a) hbc
    rw [xorOp_involution a (by have := hb.1; omega),
      xorOp_involution a (by have := hc.1; omega)] at h
    exact h
  rw [Set.ncard_image_of_injOn hinj]
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
  omega

theorem xorOp_count_finite (a N : ℕ) :
    {b : ℕ | 0 < b ∧ xorOp a b ≤ N}.Finite := by
  rw [xorOp_feasible_image]
  rw [← Finset.coe_Icc]
  exact (Finset.Icc 1 N).finite_toSet.image (xorOp a)

theorem xorOp_PS : PS xorOp := by
  intro a N L b c ha hb hc hN hL
  simp only [xorOp_count] at *
  omega

theorem xorOp_PI : PI xorOp := by
  intro a N L b c ha hb hc hN hL
  simp only [xorOp_count] at *
  omega

theorem xorOp_not_multiplication : ¬ IsMultiplication xorOp := by
  intro h
  have h22 := h 2 2 (by omega) (by omega)
  norm_num [xorOp] at h22

end PoolingMultiplication
