import PoolingMultiplication.Counting

/-!
# Carries and distinct row outputs

These lemmas record the manuscript's displayed consequences explicitly.
In particular, the recurrence for *row outputs* follows from injectivity,
not merely from a recurrence for the number of partners.
-/

namespace PoolingMultiplication

theorem leftIdentity_of_comm {op : Operation} (hu : RightIdentity op)
    (hc : Comm op) {b : ℕ} (hb : 0 < b) : op 1 b = b := by
  rw [hc 1 b (by omega) hb, hu b hb]

theorem columnStrict_of_comm {op : Operation} (hs : RowStrict op)
    (hc : Comm op) {a b c : ℕ} (ha : 0 < a) (hab : a < b)
    (hposc : 0 < c) : op a c < op b c := by
  rw [hc a c ha hposc, hc b c (by omega) hposc]
  exact hs c a b hposc ha hab

theorem row_lower_bound {op : Operation} (hu : RightIdentity op)
    (hs : RowStrict op) {a : ℕ} (ha : 0 < a) :
    ∀ b : ℕ, 0 < b → a + b - 1 ≤ op a b := by
  intro b hb
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  induction k with
  | zero => simpa using (hu a ha).ge
  | succ k ih =>
    have hi := ih (by omega)
    change a + (k + 1) - 1 ≤ op a (k + 1) at hi
    change a + (k + 2) - 1 ≤ op a (k + 2)
    have h := hs a (k + 1) (k + 2) ha (by omega) (by omega)
    omega

theorem row_injective_positive {op : Operation} (hs : RowStrict op)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (heq : op a b = op a c) : b = c := by
  rcases lt_trichotomy b c with h | h | h
  · have h' := hs a b c ha hb h
    omega
  · exact h
  · have h' := hs a c b ha hc h
    omega

theorem carry_exists {op : Operation} (hp : Positive op) (hs : RowStrict op)
    (hPS : PS op) (hPI : PI op) {a : ℕ} (ha : 0 < a) (N L : ℕ) :
    ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧
      count op a (N + L) = count op a N + count op a L + ε := by
  have hlo := (ps_iff_count_superadd hp hs).mp hPS a N L ha
  have hhi := pi_iff_count_subadd_one.mp hPI a N L ha
  refine ⟨count op a (N + L) - (count op a N + count op a L), ?_, ?_⟩ <;> omega

theorem pooling_iff_row_defect {op : Operation}
    (hp : Positive op) (hs : RowStrict op) :
    (PS op ∧ PI op) ↔
      ∀ a b c, 0 < a → 0 < b → 0 < c →
        op a (b + c) ≤ op a b + op a c ∧
        op a b + op a c ≤ op a (b + c) + 1 := by
  constructor
  · rintro ⟨hPS, hPI⟩ a b c ha hb hc
    exact ⟨(ps_iff_rowSub hp hs).mp hPS a b c ha hb hc,
      (pi_iff_rowSuper hp hs).mp hPI a b c ha hb hc⟩
  · intro h
    exact ⟨(ps_iff_rowSub hp hs).mpr (fun a b c ha hb hc => (h a b c ha hb hc).1),
      (pi_iff_rowSuper hp hs).mpr (fun a b c ha hb hc => (h a b c ha hb hc).2)⟩

def rowOutputs (op : Operation) (a : ℕ) : Set ℕ :=
  op a '' {b : ℕ | 0 < b}

noncomputable def outputCount (op : Operation) (a N : ℕ) : ℕ :=
  Set.ncard {v : ℕ | v ∈ rowOutputs op a ∧ v ≤ N}

noncomputable def outputIntervalCount (op : Operation) (a N L : ℕ) : ℕ :=
  Set.ncard {v : ℕ | v ∈ rowOutputs op a ∧ N < v ∧ v ≤ N + L}

theorem outputCount_eq_count {op : Operation} (hs : RowStrict op)
    {a : ℕ} (ha : 0 < a) (N : ℕ) : outputCount op a N = count op a N := by
  have himage : {v : ℕ | v ∈ rowOutputs op a ∧ v ≤ N} =
      op a '' {b : ℕ | 0 < b ∧ op a b ≤ N} := by
    ext v
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, hN⟩
      exact ⟨b, ⟨hb, hN⟩, rfl⟩
    · rintro ⟨b, ⟨hb, hN⟩, rfl⟩
      exact ⟨⟨b, hb, rfl⟩, hN⟩
  unfold outputCount count
  rw [himage]
  apply Set.ncard_image_of_injOn
  intro b hb c hc heq
  exact row_injective_positive hs ha hb.1 hc.1 heq

theorem outputIntervalCount_eq_intervalCount {op : Operation} (hs : RowStrict op)
    {a : ℕ} (ha : 0 < a) (N L : ℕ) :
    outputIntervalCount op a N L = intervalCount op a N L := by
  have himage : {v : ℕ | v ∈ rowOutputs op a ∧ N < v ∧ v ≤ N + L} =
      op a '' {b : ℕ | 0 < b ∧ N < op a b ∧ op a b ≤ N + L} := by
    ext v
    constructor
    · rintro ⟨⟨b, hb, rfl⟩, hN, hL⟩
      exact ⟨b, ⟨hb, hN, hL⟩, rfl⟩
    · rintro ⟨b, ⟨hb, hN, hL⟩, rfl⟩
      exact ⟨⟨b, hb, rfl⟩, hN, hL⟩
  unfold outputIntervalCount intervalCount
  rw [himage]
  apply Set.ncard_image_of_injOn
  intro b hb c hc heq
  exact row_injective_positive hs ha hb.1 hc.1 heq

theorem outputIntervalCount_alternatives {op : Operation}
    (hp : Positive op) (hs : RowStrict op) (hPS : PS op) (hPI : PI op)
    {a : ℕ} (ha : 0 < a) (N L : ℕ) :
    outputIntervalCount op a N L = count op a L ∨
      outputIntervalCount op a N L = count op a L + 1 := by
  rw [outputIntervalCount_eq_intervalCount hs ha N L]
  exact interval_count_alternatives hp hs hPS hPI ha N L

end PoolingMultiplication
