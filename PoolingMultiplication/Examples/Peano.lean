import PoolingMultiplication.Factorial
import PoolingMultiplication.Counting

/-! # Shifted addition: sufficiency without insufficiency -/

namespace PoolingMultiplication.Peano

def op : Operation := fun a b => a + b - 1

theorem positive : Positive op := by
  intro a b ha hb
  simp only [op]
  omega

theorem rightIdentity : RightIdentity op := by
  intro a ha
  simp [op]

theorem rowStrict : RowStrict op := by
  intro a b c ha hb hbc
  simp only [op]
  omega

theorem comm : Comm op := by
  intro a b ha hb
  simp [op, Nat.add_comm]

theorem assoc : Assoc op := by
  intro a b c ha hb hc
  simp only [op]
  omega

/-- The positive labels are identified with the additive monoid of naturals. -/
theorem shift_product (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    op a b - 1 = (a - 1) + (b - 1) := by
  unfold op
  omega

theorem shift_inverse (a : ℕ) (ha : 0 < a) : (a - 1) + 1 = a := by
  omega

theorem rowSub : RowSub op := by
  intro a b c ha hb hc
  simp only [op]
  omega

theorem satisfies_PS : PS op :=
  (ps_iff_rowSub positive rowStrict).mpr rowSub

theorem count_formula (a N : ℕ) (ha : 0 < a) :
    count op a N = N - (a - 1) := by
  apply count_eq_of_threshold
  intro b hb
  simp only [op]
  omega

theorem not_PI : ¬ PI op := by
  intro h
  have h3 : count op 3 3 = 1 := by rw [count_formula 3 3 (by omega)]
  have h6 : count op 3 6 = 4 := by rw [count_formula 3 6 (by omega)]
  have hh := h 3 3 3 2 2 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  norm_num at hh
  omega

theorem atom_iff (a : ℕ) : Atom op a ↔ a = 2 := by
  constructor
  · rintro ⟨ha, h⟩
    have hh := h 2 (a - 1) (by omega) (by omega) (by simp only [op]; omega)
    omega
  · rintro rfl
    constructor
    · omega
    · intro b c hb hc h
      simp only [op] at h
      omega

theorem fold_replicate (k : ℕ) :
    (List.replicate k 2).foldr op 1 = k + 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, op]; omega

theorem factorial : Factorial op := by
  constructor
  · intro n hn
    refine ⟨List.replicate (n - 1) 2, ?_, ?_⟩
    · intro a ha
      exact (atom_iff a).mpr ((List.mem_replicate.mp ha).2)
    · rw [fold_replicate]
      omega
  · intro l k hl hk h
    have hll : l = List.replicate l.length 2 :=
      List.eq_replicate_length.mpr (fun a ha => (atom_iff a).mp (hl a ha))
    have hkk : k = List.replicate k.length 2 :=
      List.eq_replicate_length.mpr (fun a ha => (atom_iff a).mp (hk a ha))
    have hlen : l.length = k.length := by
      rw [hll, hkk, fold_replicate, fold_replicate] at h
      omega
    have heq : l = k := by rw [hll, hkk, hlen]
    exact heq ▸ List.Perm.refl k

end PoolingMultiplication.Peano
