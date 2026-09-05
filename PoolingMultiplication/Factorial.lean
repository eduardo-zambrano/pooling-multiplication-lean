import PoolingMultiplication.Basic

/-!
# Factoriality on the positive carrier

Mathlib's `UniqueFactorizationMonoid` includes a zero element. The paper's
monoids have no zero, so we state the usual full finite-factorization
property directly. An atom is a nonidentity positive element with no
decomposition into two nonidentity positive elements. Factorizations are
lists of atoms, and uniqueness means equality up to permutation.
-/

namespace PoolingMultiplication

def Atom (op : Operation) (a : ℕ) : Prop :=
  1 < a ∧ ∀ b c, 0 < b → 0 < c → op b c = a → b = 1 ∨ c = 1

def AtomList (op : Operation) (l : List ℕ) : Prop :=
  ∀ a ∈ l, Atom op a

def Factorial (op : Operation) : Prop :=
  (∀ n, 0 < n → ∃ l : List ℕ, AtomList op l ∧ l.foldr op 1 = n) ∧
  (∀ l k : List ℕ, AtomList op l → AtomList op k →
    l.foldr op 1 = k.foldr op 1 → l.Perm k)

lemma atomList_positive {op : Operation} {l : List ℕ} (h : AtomList op l) :
    ∀ a ∈ l, 0 < a := by
  intro a ha
  exact lt_trans Nat.zero_lt_one (h a ha).1

lemma foldr_positive {op : Operation} (hp : Positive op) {l : List ℕ}
    (hl : ∀ a ∈ l, 0 < a) : 0 < l.foldr op 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact hp a _ (hl a (by simp)) (ih (by
      intro b hb
      exact hl b (by simp [hb])))

end PoolingMultiplication
