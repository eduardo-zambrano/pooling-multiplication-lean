import PoolingMultiplication.Rigidity

/-!
# Classical one-unit pinning for an individual row

Subadditivity of a row and superadditivity after subtracting one place the
row within one unit of a real linear function. The proof uses an infimum
of positive-index ratios and compares their lower and upper bounds at a
common multiple. It requires neither strict monotonicity nor compatibility
between different rows.

This is only a pinning statement: it makes no assertion that arbitrary
choices within the one-unit band satisfy the pooling inequalities.
-/

namespace PoolingMultiplication

private theorem super_replicate {op : Operation} (hsuper : RowSuper op)
    (a b k : ℕ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    k * op a b + 1 ≤ op a (k * b) + k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp
    · have hi := ih hk'
      have hs := hsuper a (k * b) b ha (Nat.mul_pos hk' hb) hb
      simp only [Nat.add_mul, Nat.one_mul]
      nlinarith

private theorem row_ratio_cross_bound {op : Operation}
    (hsub : RowSub op) (hsuper : RowSuper op)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((op a b : ℝ) - 1) / b ≤ (op a c : ℝ) / c := by
  have hlo := super_replicate hsuper a b c ha hb hc
  have hup := replicate hsub a c b ha hc hb
  rw [Nat.mul_comm c b] at hlo
  have hnat : c * op a b ≤ b * op a c + c := by omega
  have hreal : (c : ℝ) * (op a b : ℝ) ≤
      (b : ℝ) * (op a c : ℝ) + c := by exact_mod_cast hnat
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  apply (div_le_div_iff₀ hb' hc').mpr
  nlinarith

/-- Each row satisfying the two threshold inequalities lies in a one-unit
band about some nonnegative real slope. No order or identity is needed. -/
theorem row_pinning {op : Operation} (hsub : RowSub op) (hsuper : RowSuper op)
    (a : ℕ) (ha : 0 < a) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ b : ℕ, 0 < b →
      θ * b ≤ (op a b : ℝ) ∧ (op a b : ℝ) ≤ θ * b + 1 := by
  let S : Set ℝ := (fun b : ℕ => (op a b : ℝ) / b) '' Set.Ici 1
  have hne : S.Nonempty := by
    refine ⟨(op a 1 : ℝ), 1, by simp, ?_⟩
    norm_num
  have hnonneg : ∀ x ∈ S, (0 : ℝ) ≤ x := by
    rintro x ⟨b, hb, rfl⟩
    positivity
  have hbdd : BddBelow S := ⟨0, hnonneg⟩
  refine ⟨sInf S, le_csInf hne hnonneg, ?_⟩
  intro b hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hlower : sInf S ≤ (op a b : ℝ) / b :=
    csInf_le hbdd ⟨b, hb, rfl⟩
  have hupper : ((op a b : ℝ) - 1) / b ≤ sInf S := by
    apply le_csInf hne
    rintro x ⟨c, hc, rfl⟩
    exact row_ratio_cross_bound hsub hsuper a b c ha hb hc
  constructor
  · exact (le_div_iff₀ hb').mp hlower
  · have h := (div_le_iff₀ hb').mp hupper
    linarith

/-- Right normalization confines the slope of row `a` to the interval
`[(a : ℝ) - 1, a]`, in addition to the one-unit pinning. -/
theorem normalized_row_pinning {op : Operation} (hunit : RightIdentity op)
    (hsub : RowSub op) (hsuper : RowSuper op) (a : ℕ) (ha : 0 < a) :
    ∃ θ : ℝ, 0 ≤ θ ∧ (a : ℝ) - 1 ≤ θ ∧ θ ≤ (a : ℝ) ∧
      ∀ b : ℕ, 0 < b →
        θ * b ≤ (op a b : ℝ) ∧ (op a b : ℝ) ≤ θ * b + 1 := by
  obtain ⟨θ, hθ, hband⟩ := row_pinning hsub hsuper a ha
  have hone := hband 1 (by omega)
  rw [hunit a ha] at hone
  norm_num at hone
  exact ⟨θ, hθ, by linarith [hone.2], hone.1, hband⟩

end PoolingMultiplication
