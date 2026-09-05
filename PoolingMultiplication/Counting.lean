import PoolingMultiplication.Basic

/-!
# Counting, threshold inversion, and the pooling principles

All counts are cardinalities of the full sets in `Basic.lean`. Strict order
and positivity imply finiteness; no truncation is built into the definition.
-/

namespace PoolingMultiplication

variable {op : Operation} {a b N L K : ℕ}

theorem partner_le_output (hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (b : ℕ) : b ≤ op a b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb : b = 0
    · subst b
      exact hp a 1 ha (by omega)
    · have h := hs a b (b + 1) ha (Nat.pos_of_ne_zero hb) (by omega)
      omega

theorem count_finite (hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (N : ℕ) : {b : ℕ | 0 < b ∧ op a b ≤ N}.Finite := by
  apply (Finset.Icc 1 N).finite_toSet.subset
  intro b hb
  simp only [Finset.mem_coe, Finset.mem_Icc]
  have hout := partner_le_output hp hs ha b
  exact ⟨hb.1, hout.trans hb.2⟩

theorem count_eq_of_threshold
    (h : ∀ b : ℕ, 0 < b → (op a b ≤ N ↔ b ≤ K)) : count op a N = K := by
  unfold count
  have hset : {b : ℕ | 0 < b ∧ op a b ≤ N} =
      (↑(Finset.Icc 1 K) : Set ℕ) := by
    ext b
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc]
    constructor
    · intro hb
      exact ⟨hb.1, (h b hb.1).mp hb.2⟩
    · intro hb
      exact ⟨hb.1, (h b hb.1).mpr hb.2⟩
  rw [hset, Set.ncard_coe_finset, Nat.card_Icc]
  omega

theorem count_mono (hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (hNL : N ≤ L) : count op a N ≤ count op a L := by
  exact Set.ncard_le_ncard (fun _ hb => ⟨hb.1, hb.2.trans hNL⟩)
    (count_finite hp hs ha L)

theorem count_zero (hp : Positive op) (ha : 0 < a) : count op a 0 = 0 := by
  apply count_eq_of_threshold
  intro b hb
  have h := hp a b ha hb
  omega

theorem count_threshold (hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (hb : 0 < b) : b ≤ count op a N ↔ op a b ≤ N := by
  constructor
  · intro hcount
    by_contra hout
    have hsubset : {j : ℕ | 0 < j ∧ op a j ≤ N} ⊆
        (↑(Finset.Icc 1 (b - 1)) : Set ℕ) := by
      intro j hj
      simp only [Finset.mem_coe, Finset.mem_Icc]
      refine ⟨hj.1, ?_⟩
      by_contra hjb
      have hbj : b ≤ j := by omega
      rcases eq_or_lt_of_le hbj with heq | hlt
      · subst j
        exact hout hj.2
      · have h := hs a b j ha hb hlt
        exact hout (h.le.trans hj.2)
    have hcard := Set.ncard_le_ncard hsubset (Finset.Icc 1 (b - 1)).finite_toSet
    simp only [Set.ncard_coe_finset, Nat.card_Icc] at hcard
    change count op a N ≤ (b - 1) + 1 - 1 at hcard
    omega
  · intro hout
    have hsubset : (↑(Finset.Icc 1 b) : Set ℕ) ⊆
        {j : ℕ | 0 < j ∧ op a j ≤ N} := by
      intro j hj
      simp only [Finset.mem_coe, Finset.mem_Icc] at hj
      refine ⟨hj.1, ?_⟩
      rcases eq_or_lt_of_le hj.2 with heq | hlt
      · subst j
        exact hout
      · exact (hs a j b ha hj.1 hlt).le.trans hout
    have hcard := Set.ncard_le_ncard hsubset (count_finite hp hs ha N)
    simpa only [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] using hcard

theorem count_lt_iff (hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (hb : 0 < b) : count op a N < b ↔ N < op a b := by
  have h := count_threshold hp hs (N := N) ha hb
  omega

theorem count_at_row (_hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (hb : 0 < b) : count op a (op a b) = b := by
  apply count_eq_of_threshold
  intro j hj
  constructor
  · intro hout
    by_contra h
    have hlt := hs a b j ha hb (by omega)
    omega
  · intro hjb
    rcases eq_or_lt_of_le hjb with rfl | hlt
    · exact le_rfl
    · exact (hs a j b ha hj hlt).le

theorem ps_iff_count_superadd (hp : Positive op) (hs : RowStrict op) :
    PS op ↔ ∀ a N L, 0 < a →
      count op a N + count op a L ≤ count op a (N + L) := by
  constructor
  · intro h a N L ha
    by_cases hn : count op a N = 0
    · simpa [hn] using count_mono hp hs ha (show L ≤ N + L by omega)
    by_cases hl : count op a L = 0
    · simpa [hl] using count_mono hp hs ha (show N ≤ N + L by omega)
    exact h a N L _ _ ha (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hl)
      le_rfl le_rfl
  · intro h a N L b c ha hb hc hN hL
    exact (Nat.add_le_add hN hL).trans (h a N L ha)

theorem pi_iff_count_subadd_one :
    PI op ↔ ∀ a N L, 0 < a →
      count op a (N + L) ≤ count op a N + count op a L + 1 := by
  constructor
  · intro h a N L ha
    have h' := h a N L (count op a N + 1) (count op a L + 1)
      ha (by omega) (by omega) (by omega) (by omega)
    omega
  · intro h a N L b c ha hb hc hN hL
    have h' := h a N L ha
    omega

theorem ps_iff_rowSub (hp : Positive op) (hs : RowStrict op) : PS op ↔ RowSub op := by
  constructor
  · intro h a b c ha hb hc
    apply (count_threshold hp hs ha (Nat.add_pos_left hb c)).mp
    exact h a (op a b) (op a c) b c ha hb hc
      ((count_threshold hp hs ha hb).mpr le_rfl)
      ((count_threshold hp hs ha hc).mpr le_rfl)
  · intro h a N L b c ha hb hc hN hL
    apply (count_threshold hp hs ha (Nat.add_pos_left hb c)).mpr
    have hN' := (count_threshold hp hs ha hb).mp hN
    have hL' := (count_threshold hp hs ha hc).mp hL
    exact (h a b c ha hb hc).trans (Nat.add_le_add hN' hL')

theorem pi_iff_rowSuper (hp : Positive op) (hs : RowStrict op) : PI op ↔ RowSuper op := by
  constructor
  · intro h a b c ha hb hc
    have hpb := hp a b ha hb
    have hpc := hp a c ha hc
    have hN := (count_lt_iff hp hs ha hb (N := op a b - 1)).mpr (by omega)
    have hL := (count_lt_iff hp hs ha hc (N := op a c - 1)).mpr (by omega)
    have h' := h a (op a b - 1) (op a c - 1) b c ha hb hc hN hL
    have hout := (count_lt_iff hp hs ha (Nat.add_pos_left hb c)).mp h'
    omega
  · intro h a N L b c ha hb hc hN hL
    apply (count_lt_iff hp hs ha (Nat.add_pos_left hb c)).mpr
    have hN' := (count_lt_iff hp hs ha hb).mp hN
    have hL' := (count_lt_iff hp hs ha hc).mp hL
    have hrow := h a b c ha hb hc
    omega

noncomputable def intervalCount (op : Operation) (a N L : ℕ) : ℕ :=
  Set.ncard {b : ℕ | 0 < b ∧ N < op a b ∧ op a b ≤ N + L}

theorem interval_count_eq (hp : Positive op) (hs : RowStrict op)
    (ha : 0 < a) (N L : ℕ) :
    intervalCount op a N L = count op a (N + L) - count op a N := by
  unfold intervalCount count
  have hset : {b : ℕ | 0 < b ∧ N < op a b ∧ op a b ≤ N + L} =
      {b : ℕ | 0 < b ∧ op a b ≤ N + L} \ {b : ℕ | 0 < b ∧ op a b ≤ N} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_diff]
    omega
  rw [hset]
  apply Set.ncard_diff
  · intro b hb
    exact ⟨hb.1, hb.2.trans (Nat.le_add_right N L)⟩
  · exact count_finite hp hs ha N

theorem interval_count_alternatives (hp : Positive op) (hs : RowStrict op)
    (hPS : PS op) (hPI : PI op) (ha : 0 < a) (N L : ℕ) :
    intervalCount op a N L = count op a L ∨
      intervalCount op a N L = count op a L + 1 := by
  rw [interval_count_eq hp hs ha N L]
  have hlo := (ps_iff_count_superadd hp hs).mp hPS a N L ha
  have hhi := pi_iff_count_subadd_one.mp hPI a N L ha
  omega

end PoolingMultiplication
