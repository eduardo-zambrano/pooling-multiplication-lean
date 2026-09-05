import Mathlib

/-!
# Operations and their genuine feasible-partner counts

The paper's carrier is the positive integers. We use natural-number functions,
with every structural hypothesis restricted to positive inputs. Values at zero
are deliberately irrelevant. Capacities, in contrast, may be zero.

The count uses the full set of positive partners, not an artificial finite
cutoff. Finiteness is proved separately, so this definition also applies to
the nonmonotone permutation example.
-/

namespace PoolingMultiplication

abbrev Operation := ℕ → ℕ → ℕ

def Positive (op : Operation) : Prop :=
  ∀ a b, 0 < a → 0 < b → 0 < op a b

def RightIdentity (op : Operation) : Prop :=
  ∀ a, 0 < a → op a 1 = a

def RowStrict (op : Operation) : Prop :=
  ∀ a b c, 0 < a → 0 < b → b < c → op a b < op a c

def Comm (op : Operation) : Prop :=
  ∀ a b, 0 < a → 0 < b → op a b = op b a

def Assoc (op : Operation) : Prop :=
  ∀ a b c, 0 < a → 0 < b → 0 < c → op (op a b) c = op a (op b c)

noncomputable def count (op : Operation) (a N : ℕ) : ℕ :=
  Set.ncard {b : ℕ | 0 < b ∧ op a b ≤ N}

def PS (op : Operation) : Prop :=
  ∀ a N L b c, 0 < a → 0 < b → 0 < c →
    b ≤ count op a N → c ≤ count op a L → b + c ≤ count op a (N + L)

def PI (op : Operation) : Prop :=
  ∀ a N L b c, 0 < a → 0 < b → 0 < c →
    count op a N < b → count op a L < c → count op a (N + L) < b + c

def RowSub (op : Operation) : Prop :=
  ∀ a b c, 0 < a → 0 < b → 0 < c → op a (b + c) ≤ op a b + op a c

def RowSuper (op : Operation) : Prop :=
  ∀ a b c, 0 < a → 0 < b → 0 < c → op a b + op a c ≤ op a (b + c) + 1

def IsMultiplication (op : Operation) : Prop :=
  ∀ a b, 0 < a → 0 < b → op a b = a * b

end PoolingMultiplication
