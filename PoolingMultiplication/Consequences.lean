import PoolingMultiplication.Main
import PoolingMultiplication.Arithmetic

/-! # Factoriality and arithmetic counts for any operation satisfying pooling -/

namespace PoolingMultiplication

theorem count_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (a N : ℕ) (ha : 0 < a) : count op a N = N / a := by
  rw [← mul_count ha N]
  unfold count
  apply congrArg Set.ncard
  ext b
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hb, hout⟩
    exact ⟨hb, by rwa [hmul a b ha hb] at hout⟩
  · rintro ⟨hb, hout⟩
    exact ⟨hb, by rwa [hmul a b ha hb]⟩

theorem pairCount_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (n : ℕ) (hn : 0 < n) : pairCount op n = n.divisors.card := by
  rw [← mul_pair_count hn]
  unfold pairCount
  apply congrArg Set.ncard
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, hb, hout⟩
    exact ⟨ha, hb, by rwa [hmul p.1 p.2 ha hb] at hout⟩
  · rintro ⟨ha, hb, hout⟩
    exact ⟨ha, hb, by rwa [hmul p.1 p.2 ha hb]⟩

theorem atom_of_multiplication_iff {op : Operation} (hmul : IsMultiplication op)
    (a : ℕ) : Atom op a ↔ Atom Nat.mul a := by
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro b c hb hc heq
    exact h b c hb hc (by rwa [hmul b c hb hc])
  · rintro ⟨ha, h⟩
    refine ⟨ha, ?_⟩
    intro b c hb hc heq
    exact h b c hb hc (by rwa [hmul b c hb hc] at heq)

theorem foldr_of_multiplication {op : Operation} (hmul : IsMultiplication op)
    (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    0 < l.foldr op 1 ∧ l.foldr op 1 = l.foldr Nat.mul 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ht := ih (by
      intro b hb
      exact hl b (by simp [hb]))
    simp only [List.foldr_cons]
    rw [hmul a (l.foldr op 1) ha ht.1]
    exact ⟨Nat.mul_pos ha ht.1, by rw [ht.2]; rfl⟩

theorem factorial_of_multiplication {op : Operation} (hmul : IsMultiplication op) :
    Factorial op := by
  constructor
  · intro n hn
    obtain ⟨l, hl, heq⟩ := mul_factorial.1 n hn
    refine ⟨l, ?_, ?_⟩
    · intro a ha
      exact (atom_of_multiplication_iff hmul a).mpr (hl a ha)
    · exact (foldr_of_multiplication hmul l (atomList_positive hl)).2.trans heq
  · intro l k hl hk heq
    have hl' : AtomList Nat.mul l := by
      intro a ha
      exact (atom_of_multiplication_iff hmul a).mp (hl a ha)
    have hk' : AtomList Nat.mul k := by
      intro a ha
      exact (atom_of_multiplication_iff hmul a).mp (hk a ha)
    apply mul_factorial.2 l k hl' hk'
    change l.foldr Nat.mul 1 = k.foldr Nat.mul 1
    exact (foldr_of_multiplication hmul l (atomList_positive hl)).2.symm.trans
      (heq.trans (foldr_of_multiplication hmul k (atomList_positive hk)).2)

/-- Corollary 4.2: associativity suffices, with no factoriality hypothesis. -/
theorem ordered_monoid_corollary {op : Operation} (hpos : Positive op)
    (hunit : RightIdentity op) (hstrict : RowStrict op) (hassoc : Assoc op)
    (hps : PS op) (hpi : PI op) :
    IsMultiplication op ∧ Comm op ∧ Factorial op ∧
    (∀ a N, 0 < a → count op a N = N / a) ∧
    (∀ n, 0 < n → pairCount op n = n.divisors.card) := by
  have hmul := (pooling_characterization_assoc hpos hunit hstrict hassoc).mp ⟨hps, hpi⟩
  exact ⟨hmul, comm_of_multiplication hmul, factorial_of_multiplication hmul,
    count_of_multiplication hmul, pairCount_of_multiplication hmul⟩

end PoolingMultiplication
