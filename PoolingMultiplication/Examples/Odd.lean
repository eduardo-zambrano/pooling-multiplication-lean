import PoolingMultiplication.Factorial
import PoolingMultiplication.Counting

/-! # Multiplication on the positive odd integers: insufficiency without sufficiency -/

namespace PoolingMultiplication.Odd

/-- A subtraction-safe expression for `2*a*b-a-b+1` on positive inputs. -/
def op : Operation := fun a b => a + b - 1 + 2 * (a - 1) * (b - 1)

def norm (a : ℕ) : ℕ := 2 * a - 1

lemma op_succ (a b : ℕ) : op (a + 1) (b + 1) = 2 * a * b + a + b + 1 := by
  simp only [op, Nat.add_sub_cancel]
  omega

lemma norm_succ (a : ℕ) : norm (a + 1) = 2 * a + 1 := by
  simp only [norm]
  omega

theorem positive : Positive op := by
  intro a b ha hb
  unfold op
  omega

theorem rightIdentity : RightIdentity op := by
  intro a ha
  simp [op]

theorem rowStrict : RowStrict op := by
  intro a b c ha hb hbc
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_trans hb hbc))
  simp only [Nat.succ_eq_add_one, op_succ] at *
  nlinarith

theorem comm : Comm op := by
  intro a b ha hb
  unfold op
  rw [Nat.add_comm a b]
  congr 1
  ring

lemma norm_positive (a : ℕ) (ha : 0 < a) : 0 < norm a := by
  unfold norm
  omega

lemma norm_injective {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : norm a = norm b) : a = b := by
  unfold norm at h
  omega

lemma norm_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    norm (op a b) = norm a * norm b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp only [Nat.succ_eq_add_one, op_succ, norm_succ]
  ring

theorem assoc : Assoc op := by
  intro a b c ha hb hc
  apply norm_injective (positive _ _ (positive _ _ ha hb) hc)
    (positive _ _ ha (positive _ _ hb hc))
  rw [norm_mul _ _ (positive _ _ ha hb) hc, norm_mul _ _ ha hb,
    norm_mul _ _ ha (positive _ _ hb hc), norm_mul _ _ hb hc, Nat.mul_assoc]

lemma row_linear (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    op a b + (a - 1) = (2 * a - 1) * b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp only [Nat.succ_eq_add_one, op_succ, Nat.add_sub_cancel]
  have h : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  rw [h]
  ring

/-- Agreement with the numerical formula displayed in the paper. -/
theorem formula (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    op a b = 2 * a * b - a - b + 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp only [Nat.succ_eq_add_one, op_succ]
  have h : 2 * (a + 1) * (b + 1) = 2 * a * b + 2 * a + 2 * b + 2 := by ring
  rw [h]
  omega

theorem row_increment (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    op a (b + 1) = op a b + (2 * a - 1) := by
  have h := row_linear a b ha hb
  have h' := row_linear a (b + 1) ha (by omega)
  rw [Nat.mul_add, Nat.mul_one] at h'
  omega

theorem rowSuper : RowSuper op := by
  intro a b c ha hb hc
  have hab := row_linear a b ha hb
  have hac := row_linear a c ha hc
  have habc := row_linear a (b + c) ha (by omega)
  rw [Nat.mul_add] at habc
  omega

theorem satisfies_PI : PI op :=
  (pi_iff_rowSuper positive rowStrict).mpr rowSuper

theorem count_formula (a N : ℕ) (ha : 0 < a) :
    count op a N = (N + a - 1) / (2 * a - 1) := by
  apply count_eq_of_threshold
  intro b hb
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * a - 1)]
  have h := row_linear a b ha hb
  rw [Nat.mul_comm b] at ⊢
  omega

theorem not_PS : ¬ PS op := by
  intro h
  have h2 : count op 2 2 = 1 := by rw [count_formula 2 2 (by omega)]
  have h4 : count op 2 4 = 1 := by rw [count_formula 2 4 (by omega)]
  have hh := h 2 2 2 1 1 (by omega) (by omega) (by omega)
    (by omega) (by omega)
  norm_num at hh
  omega

lemma norm_injective_all : Function.Injective norm := by
  intro a b h
  unfold norm at h
  omega

lemma norm_odd (a : ℕ) (ha : 0 < a) : _root_.Odd (norm a) := by
  apply odd_iff_exists_bit1.mpr
  refine ⟨a - 1, ?_⟩
  unfold norm
  omega

/-- The label map is onto the positive odd numbers. -/
def denorm (p : ℕ) : ℕ := (p + 1) / 2

lemma norm_denorm {p : ℕ} (hp : _root_.Odd p) : norm (denorm p) = p := by
  obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hp
  unfold norm denorm
  omega

lemma denorm_positive {p : ℕ} (hp : _root_.Odd p) : 0 < denorm p := by
  obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hp
  unfold denorm
  omega

theorem atom_iff_prime (a : ℕ) (ha : 0 < a) :
    Atom op a ↔ Nat.Prime (norm a) := by
  constructor
  · rintro ⟨ha1, hatom⟩
    change Irreducible (norm a)
    constructor
    · simp only [Nat.isUnit_iff]
      unfold norm
      omega
    · intro p q hpq
      have hodd : _root_.Odd (p * q) := by rw [← hpq]; exact norm_odd a ha
      have hpodd := (Nat.odd_mul.mp hodd).1
      have hqodd := (Nat.odd_mul.mp hodd).2
      have hpd := denorm_positive hpodd
      have hqd := denorm_positive hqodd
      have hprod : op (denorm p) (denorm q) = a := by
        apply norm_injective (positive _ _ hpd hqd) ha
        rw [norm_mul _ _ hpd hqd, norm_denorm hpodd, norm_denorm hqodd]
        exact hpq.symm
      have hunits := hatom _ _ hpd hqd hprod
      simp only [Nat.isUnit_iff]
      rcases hunits with hp | hq
      · left
        have hpn := norm_denorm hpodd
        rw [hp] at hpn
        norm_num [norm] at hpn
        exact hpn.symm
      · right
        have hqn := norm_denorm hqodd
        rw [hq] at hqn
        norm_num [norm] at hqn
        exact hqn.symm
  · intro hprime
    constructor
    · have h := hprime.one_lt
      unfold norm at h
      omega
    · intro b c hb hc hbc
      have hprod : norm a = norm b * norm c := by
        rw [← hbc, norm_mul _ _ hb hc]
      have hh := hprime.isUnit_or_isUnit hprod
      simp only [Nat.isUnit_iff] at hh
      unfold norm at hh
      omega

lemma norm_fold (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    norm (l.foldr op 1) = (l.map norm).prod := by
  induction l with
  | nil => norm_num [norm]
  | cons a l ih =>
    have ha := hl a (by simp)
    have htl : ∀ b ∈ l, 0 < b := by
      intro b hb
      exact hl b (by simp [hb])
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [norm_mul _ _ ha (foldr_positive positive htl), ih htl]

lemma prime_factor_odd {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ (norm n).primeFactorsList) : _root_.Odd p := by
  have hodd := norm_odd n hn
  obtain ⟨q, hq⟩ := Nat.dvd_of_mem_primeFactorsList hp
  rw [hq] at hodd
  exact (Nat.odd_mul.mp hodd).1

theorem factorial : Factorial op := by
  constructor
  · intro n hn
    let l := (norm n).primeFactorsList.map denorm
    have hl : AtomList op l := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      have hpodd := prime_factor_odd hn hp
      apply (atom_iff_prime _ (denorm_positive hpodd)).mpr
      rw [norm_denorm hpodd]
      exact Nat.prime_of_mem_primeFactorsList hp
    refine ⟨l, hl, ?_⟩
    apply norm_injective_all
    rw [norm_fold l (atomList_positive hl)]
    have hmap : l.map norm = (norm n).primeFactorsList := by
      change ((norm n).primeFactorsList.map denorm).map norm = _
      rw [List.map_map]
      calc
        _ = (norm n).primeFactorsList.map id := by
          apply List.map_congr_left
          intro p hp
          exact norm_denorm (prime_factor_odd hn hp)
        _ = _ := List.map_id' _
    rw [hmap]
    exact Nat.prod_primeFactorsList (Nat.ne_of_gt (norm_positive n hn))
  · intro l k hl hk hprod
    have hpl : ∀ p ∈ l.map norm, Nat.Prime p := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact (atom_iff_prime a (atomList_positive hl a ha)).mp (hl a ha)
    have hpk : ∀ p ∈ k.map norm, Nat.Prime p := by
      intro p hp
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
      exact (atom_iff_prime a (atomList_positive hk a ha)).mp (hk a ha)
    have heq : (l.map norm).prod = (k.map norm).prod := by
      rw [← norm_fold l (atomList_positive hl),
        ← norm_fold k (atomList_positive hk), hprod]
    have hperm := (Nat.primeFactorsList_unique heq hpl).trans
      (Nat.primeFactorsList_unique rfl hpk).symm
    exact (List.map_perm_map_iff norm_injective_all).mp hperm

end PoolingMultiplication.Odd
