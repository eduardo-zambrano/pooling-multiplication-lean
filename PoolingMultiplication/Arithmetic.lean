import PoolingMultiplication.Counting
import PoolingMultiplication.Factorial

/-!
# The arithmetic conclusions

The feasible-partner count is the ordinary quotient, the ordered two-factor
count is the number of divisors, and factoriality is supplied by the full
fundamental theorem of arithmetic, with existence and uniqueness certificates.
-/

namespace PoolingMultiplication

theorem mul_positive : Positive (· * ·) := by
  intro a b ha hb
  exact Nat.mul_pos ha hb

theorem mul_rowStrict : RowStrict (· * ·) := by
  intro a b c ha hb hbc
  exact Nat.mul_lt_mul_of_pos_left hbc ha

theorem mul_rightIdentity : RightIdentity (· * ·) := by
  intro a ha
  exact Nat.mul_one a

theorem mul_rowSub : RowSub (· * ·) := by
  intro a b c ha hb hc
  simp [Nat.mul_add]

theorem mul_rowSuper : RowSuper (· * ·) := by
  intro a b c ha hb hc
  simp [Nat.mul_add]

theorem mul_ps : PS (· * ·) :=
  (ps_iff_rowSub mul_positive mul_rowStrict).mpr mul_rowSub

theorem mul_pi : PI (· * ·) :=
  (pi_iff_rowSuper mul_positive mul_rowStrict).mpr mul_rowSuper

theorem mul_count {a : ℕ} (ha : 0 < a) (N : ℕ) :
    count (· * ·) a N = N / a := by
  apply count_eq_of_threshold
  intro b hb
  simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).symm

noncomputable def pairCount (op : Operation) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ op p.1 p.2 = n}

theorem mul_pair_count {n : ℕ} (hn : 0 < n) :
    pairCount (· * ·) n = n.divisors.card := by
  unfold pairCount
  have hset : {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.2 = n} =
      (↑n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    ext p
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_divisorsAntidiagonal]
    constructor
    · intro hp
      exact ⟨hp.2.2, Nat.ne_zero_of_lt hn⟩
    · intro hp
      have hprod : 0 < p.1 * p.2 := by omega
      exact ⟨by nlinarith, by nlinarith, hp.1⟩
  rw [hset, Set.ncard_coe_finset]
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    apply Nat.mem_divisors.mpr
    exact ⟨⟨p.2, (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩,
      Nat.ne_zero_of_lt hn⟩
  · intro p hp q hq heq
    have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hq' := (Nat.mem_divisorsAntidiagonal.mp hq).1
    have hppos : 0 < p.1 := by
      have hprod : 0 < p.1 * p.2 := by omega
      nlinarith
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left hppos
    simpa only [heq] using hp'.trans hq'.symm
  · intro a ha
    have hadvd := (Nat.mem_divisors.mp ha).1
    refine ⟨(a, n / a), ?_, rfl⟩
    apply Nat.mem_divisorsAntidiagonal.mpr
    exact ⟨Nat.mul_div_cancel' hadvd, Nat.ne_zero_of_lt hn⟩

theorem mul_atom_iff_prime (p : ℕ) : Atom (· * ·) p ↔ Nat.Prime p := by
  constructor
  · intro h
    apply Nat.prime_def_lt.mpr
    refine ⟨h.1, ?_⟩
    intro m hmp hdiv
    obtain ⟨c, heq⟩ := hdiv
    have hprod : 0 < m * c := by omega
    rcases h.2 m c (by nlinarith) (by nlinarith) heq.symm with hm | hc
    · exact hm
    · subst c
      simp only [Nat.mul_one] at heq
      omega
  · intro h
    refine ⟨h.one_lt, ?_⟩
    intro b c hb hc hbc
    rcases h.eq_one_or_self_of_dvd b ⟨c, hbc.symm⟩ with hbone | hbp
    · exact Or.inl hbone
    · right
      apply Nat.eq_of_mul_eq_mul_left hb
      simpa only [Nat.mul_one, hbp] using hbc

theorem mul_factorial : Factorial (· * ·) := by
  constructor
  · intro n hn
    refine ⟨n.primeFactorsList, ?_, ?_⟩
    · intro p hp
      exact (mul_atom_iff_prime p).mpr (Nat.prime_of_mem_primeFactorsList hp)
    · change n.primeFactorsList.prod = n
      exact Nat.prod_primeFactorsList (Nat.ne_zero_of_lt hn)
  · intro l k hl hk heq
    change l.prod = k.prod at heq
    have hlprime : ∀ p ∈ l, Nat.Prime p := by
      intro p hp
      exact (mul_atom_iff_prime p).mp (hl p hp)
    have hkprime : ∀ p ∈ k, Nat.Prime p := by
      intro p hp
      exact (mul_atom_iff_prime p).mp (hk p hp)
    exact (Nat.primeFactorsList_unique rfl hlprime).trans
      (Nat.primeFactorsList_unique heq.symm hkprime).symm

end PoolingMultiplication
