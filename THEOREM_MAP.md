# Manuscript-to-Lean theorem map

Reference: Eduardo Zambrano, **Multiplication from two pooling principles**,
September 5, 2026 base manuscript, `pooling_and_multiplication.tex`.
Numbering below is the manuscript's numbering, not declaration order.

Every Lean name below is in the namespace `PoolingMultiplication`.
The prefixes `Peano.` and `Odd.` are additional namespaces. The public
import is [`PoolingMultiplication.lean`](PoolingMultiplication.lean).
This map distinguishes mathematical statements from particular choices
of proof or notation in the manuscript.

## Carrier, definitions, and preliminary consequences

| Manuscript item | Lean declarations | Translation |
|---|---|---|
| Positive-integer binary operation | `Operation`, `Positive` in [Basic](PoolingMultiplication/Basic.lean) | Functions have type `ℕ → ℕ → ℕ`; positivity and all structural laws are restricted to positive inputs. Values at zero are immaterial. |
| (2.1), right identity | `RightIdentity` | `op a 1 = a` for positive `a`. |
| (2.2), strict rows | `RowStrict` | Strict increase in the positive partner variable; first-coordinate monotonicity is not assumed. |
| Associativity or commutativity | `Assoc`, `Comm` | These are separate hypotheses, not a bundled monoid typeclass. |
| (2.3), feasible-partner count | `count` | `Set.ncard` of the full set of positive feasible partners, with no artificial cutoff. |
| `a ⋆ j ≥ a + j − 1` before (2.4) | `row_lower_bound` in [Supplement](PoolingMultiplication/Supplement.lean) | Uses right identity and strict rows. |
| Every count is finite | `partner_le_output`, `count_finite` in [Counting](PoolingMultiplication/Counting.lean) | Partners are bounded by their outputs, so the full feasible set lies in a finite interval. |
| `M_a(0) = 0` | `count_zero` | Positivity suffices. |
| Feasible partners are an initial segment; (2.4) | `count_threshold`, `count_lt_iff` | `b ≤ count op a N ↔ op a b ≤ N`, and its strict negation, for positive `a,b`. |
| Counts are monotone in capacity | `count_mono` | Follows from inclusion of the genuine feasible sets. |
| Counting exactly at a row threshold | `count_at_row` | `count op a (op a b) = b`. |
| Counts also count distinct row outputs | `row_injective_positive`, `rowOutputs`, `outputCount`, `outputCount_eq_count` in Supplement | Equality is proved by an injective image, not by identifying partners with outputs by definition. |
| (2.5), PS | `PS` | The implication quantifies over positive requests and nonnegative capacities. |
| (2.6), PI | `PI` | The requested insufficiency-preservation implication is used literally. |

## Theorem 2.1 and its stated structural consequences

| Manuscript result | Lean declarations |
|---|---|
| Theorem 2.1: `(PS and PI) iff ordinary multiplication`, assuming either compatibility law | `pooling_characterization` in [Main](PoolingMultiplication/Main.lean) |
| Commutative version, with no associativity hypothesis | `pooling_characterization_comm` |
| Associative version, with no commutativity hypothesis | `pooling_characterization_assoc` |
| Conclusion identifies the numerical table | `IsMultiplication`: `op a b = a * b` on positive inputs |
| Commutativity follows in the associative version | `comm_of_multiplication` |
| Associativity follows in the commutative version | `assoc_of_multiplication` |
| The identity is two-sided | `left_identity_of_multiplication`, together with the standing `RightIdentity` hypothesis |
| Strict increase in both arguments | `first_strict_of_multiplication`, together with the standing `RowStrict` hypothesis |
| Left and right cancellation | `cancel_left_of_multiplication`, `cancel_right_of_multiplication` |
| Factoriality follows | `factorial_of_multiplication` in [Consequences](PoolingMultiplication/Consequences.lean) |

The reverse implication is proved using distributivity of ordinary
multiplication and the threshold equivalences. It does not reproduce the
manuscript's optional detour through floor inequalities for arbitrary real
`x,y`. This is a different proof of the same positive-integer assertion.

## Section 3: counting, carries, and thresholds

| Manuscript result or display | Lean declarations | Details |
|---|---|---|
| Lemma 3.1, (3.1): PS iff count superadditivity | `ps_iff_count_superadd` in Counting | The Lean equivalence is stated for the family of positive rows. |
| Lemma 3.1, (3.2): PI iff upper count inequality | `pi_iff_count_subadd_one` | The bound is `count (N+L) ≤ count N + count L + 1`. |
| (3.3), a carry in `{0,1}` | `carry_exists` in Supplement | Explicitly produces `ε = 0 ∨ ε = 1` and the displayed count equality. The carry is not supplied as an assumption. |
| Count of partners whose outputs lie in `(N,N+L]` | `intervalCount`, `interval_count_eq` in Counting | Equals `count (N+L) − count N`. |
| Interval count has the two stated alternatives | `interval_count_alternatives` | The partner-count version. |
| Display involving `S_a ∩ (N,N+L]`, where `S_a` is the set of row outputs | `rowOutputs`, `outputIntervalCount`, `outputIntervalCount_eq_intervalCount`, `outputIntervalCount_alternatives` in Supplement | The distinct-output version is obtained by row injectivity; it is not silently replaced by a count of partners. |
| Lemma 3.2, (3.4): PS iff threshold subadditivity | `RowSub`, `ps_iff_rowSub` | Exactly `op a (b+c) ≤ op a b + op a c`. |
| Lemma 3.2, (3.5): PI iff threshold lower bound | `RowSuper`, `pi_iff_rowSuper` | Written without subtraction: `op a b + op a c ≤ op a (b+c) + 1`. |
| (3.6), equivalence with one-sided distributive defect | `pooling_iff_row_defect` in Supplement | Both inequalities are retained. This avoids the erroneous interpretation of a negative defect as truncated natural subtraction. |

The choices of first unaffordable capacities and requests in the proofs
are implemented inside `pi_iff_count_subadd_one` and `pi_iff_rowSuper`.
They are not additional axioms.

## Section 4: finite rigidity and arithmetic consequences

| Manuscript result or display | Lean declarations |
|---|---|
| Lemma 4.1, upper bound in (4.1) | `initial_bounds` in [Rigidity](PoolingMultiplication/Rigidity.lean) |
| Lemma 4.1, lower bound in (4.1) | `initial_bounds` gives the subtraction-free form `a*b+1 ≤ op a b+b`; `initial_lower_bound` gives `(a−1)*b+1 ≤ op a b` |
| Lemma 4.1, replication inequality (4.2) | `replicate` |
| Finite amplification using symmetry | `rigidity_of_comm` |
| Finite amplification using associativity | `rigidity_of_assoc` |
| Ordinary multiplication satisfies both principles | `mul_ps`, `mul_pi` in [Arithmetic](PoolingMultiplication/Arithmetic.lean); also `rows_of_multiplication` in Main |
| Corollary 4.2, characterization for ordered monoids | `pooling_characterization_assoc` |
| Corollary 4.2, joint conclusions under pooling | `ordered_monoid_corollary` in Consequences: multiplication, commutativity, factoriality, all row counts, and all positive two-factor counts |
| `M_a(N) = floor(N/a)` | `mul_count`, and `count_of_multiplication` for an operation recovered by the characterization |
| Definition of ordered two-factor count `F_{2,⋆}(n)` | `pairCount` in Arithmetic: cardinality of positive ordered pairs with output `n` |
| `F_{2,⋆}(n) = d(n)` | `mul_pair_count`, and `pairCount_of_multiplication` for the recovered operation |
| Divisor-to-partner correspondence in the corollary's proof | The `Finset.card_bij` proof inside `mul_pair_count`: projection to the first coordinate, with inverse pair `(a,n/a)` |
| Factoriality of multiplication | `mul_atom_iff_prime`, `mul_factorial` |
| Transfer of factoriality to any operation equal to multiplication on positive inputs | `atom_of_multiplication_iff`, `foldr_of_multiplication`, `factorial_of_multiplication` |

`Nat.divisors.card` is the independent ordinary divisor count; it is not
defined through `pairCount`. Both partner positions may contain `1`.
The factorization count is restricted to positive `n`, as in the paper.

## Section 5: every independence and structural example

For commutative examples, the generic lemmas `leftIdentity_of_comm` and
`columnStrict_of_comm` in Supplement derive the left identity and strict
first-coordinate order from the stated right identity and strict rows.

### Example 5.1: Peano operation

File: [Examples/Peano.lean](PoolingMultiplication/Examples/Peano.lean).

| Claim | Lean declarations |
|---|---|
| `a ⋆₊ b = a+b−1` | `Peano.op` |
| Positive, associative, commutative, right identity, strict rows | `Peano.positive`, `Peano.assoc`, `Peano.comm`, `Peano.rightIdentity`, `Peano.rowStrict` |
| Shift to ordinary addition | `Peano.shift_product`, `Peano.shift_inverse`; the other inverse identity is the natural successor-predecessor identity |
| Single atom `2` | `Peano.atom_iff` |
| Every positive rank is a product of copies of `2` | `Peano.fold_replicate` |
| Full existence and uniqueness of atom factorizations | `Peano.factorial` |
| `M_a(N) = max(0,N−(a−1))` | `Peano.count_formula`; natural subtraction implements the maximum with zero |
| PS holds | `Peano.rowSub`, `Peano.satisfies_PS` |
| PI fails at the displayed capacities `a=N=L=3`, `b=c=2` | `Peano.not_PI`; the proof evaluates the counts `1` and `4` exactly |

### Example 5.2: odd-integer operation

File: [Examples/Odd.lean](PoolingMultiplication/Examples/Odd.lean).

| Claim | Lean declarations |
|---|---|
| Formula `2ab−a−b+1` | `Odd.op` uses the subtraction-safe expansion `a+b−1+2(a−1)(b−1)`; `Odd.formula` proves equality with the manuscript formula on positive inputs |
| `φ(a)=2a−1` | `Odd.norm` |
| Multiplication is transported through `φ` | `Odd.norm_mul` |
| `φ` is injective, positive, and odd-valued | `Odd.norm_injective`, `Odd.norm_positive`, `Odd.norm_odd` |
| Every positive odd integer is in the image | `Odd.denorm`, `Odd.norm_denorm`, `Odd.denorm_positive` |
| Positive, associative, commutative, right identity, strict rows | `Odd.positive`, `Odd.assoc`, `Odd.comm`, `Odd.rightIdentity`, `Odd.rowStrict` |
| Row increment is `2a−1` | `Odd.row_linear`, `Odd.row_increment` |
| Atoms correspond to odd primes | `Odd.atom_iff_prime` |
| Full factoriality | `Odd.factorial`; `Odd.norm_fold` transfers atom products to ordinary prime products |
| `M_a(N)=floor((N+a−1)/(2a−1))` | `Odd.count_formula` |
| PI holds | `Odd.rowSuper`, `Odd.satisfies_PI` |
| PS fails at `a=N=L=2`, `b=c=1` | `Odd.not_PS`; both displayed counts are evaluated exactly |

The transport is certified through explicit maps and identities. It is not
packaged as a mathlib `MulEquiv` between new carrier types; that packaging
is not needed for any asserted algebraic or factoriality conclusion.

### Example 5.3: ceiling rows

File: [Examples/Ceiling.lean](PoolingMultiplication/Examples/Ceiling.lean).

| Claim | Lean declarations |
|---|---|
| `1 ◇ b=b`; otherwise `ceil((a−1/2)b)` | `diamond`: the latter is implemented exactly as `((2*a−1)*b+1)/2`; `diamond_double_bounds` supplies its integer ceiling inequalities |
| Positive outputs and two-sided identity | `diamond_positive`, `diamond_rightIdentity`, `diamond_leftIdentity` |
| Strict increase in both coordinates | `diamond_rowStrict`, `diamond_columnStrict` |
| `M_1(N)=N` | `diamond_count_one` |
| For `a≥2`, `M_a(N)=floor(N/(a−1/2))` | `diamond_count`, written as natural quotient `(2*N)/(2*a−1)` |
| Both pooling principles | `diamond_rowSub`, `diamond_rowSuper`, `diamond_PS`, `diamond_PI` |
| `2◇4=6 ≠ 7=4◇2` | Exact calculation inside `diamond_not_comm` |
| `(2◇2)◇4=10 ≠ 9=2◇(2◇4)` | Exact calculation inside `diamond_not_assoc` |

The real ceiling notation is translated into integer division, not
implemented with a real-valued ceiling function. The stated rational
threshold and count are exact integer statements.

### Remark 5.4: normalization and order

File: [Examples/Structural.lean](PoolingMultiplication/Examples/Structural.lean).

| Claim | Lean declarations |
|---|---|
| Operation `2ab` | `doubleMul` |
| Positive, associative, commutative, strict in both arguments | `doubleMul_positive`, `doubleMul_assoc`, `doubleMul_comm`, `doubleMul_rowStrict`, `doubleMul_columnStrict` |
| `M_a(N)=floor(N/(2a))` | `doubleMul_count` |
| Both pooling principles | `doubleMul_PS`, `doubleMul_PI` |
| Right normalization fails | `doubleMul_not_rightIdentity` |
| Symmetric difference transported by `a↦a−1` | `xorOp`, implemented with exact natural-number bitwise XOR |
| Positive, associative, commutative, two-sided identity | `xorOp_positive`, `xorOp_assoc`, `xorOp_comm`, `xorOp_rightIdentity`, `xorOp_leftIdentity` |
| Each positive row is a permutation | `xorOp_involution` and positivity: applying the same row twice recovers every positive input |
| Full feasible set and its finiteness | `xorOp_feasible_image`, `xorOp_count_finite` |
| `M_a(N)=N` | `xorOp_count`; cardinality is preserved by the injective image of `[1,N]` |
| Both pooling principles | `xorOp_PS`, `xorOp_PI` |
| Strict row order fails; `2⋆2=1` | `xorOp_not_rowStrict`, `xorOp_not_multiplication`, with exact small witnesses |

## Scope and intentional translation boundaries

- All named mathematical results, axioms, numbered equations, and the
  principal unnumbered consequences above have corresponding Lean
  declarations. Proof-intermediate algebraic calculations may live inside
  a theorem's proof rather than have separate public names.
- The discussion of arbitrary relabeling in the introduction is contextual:
  no general transport-of-structure library is developed here. The two
  particular transports used in the independence examples are verified.
- Mathematical interpretation, economic analogies, novelty, journal fit,
  and results cited from other papers are not machine-checked claims.
- The development does not certify later exploratory aggregate-count
  conjectures or an extension with an arbitrary defect constant.
- `Factorial` means actual existence and uniqueness, up to permutation,
  of finite lists of atoms. Associativity, commutativity, and the positive
  carrier conditions are proved separately for the relevant operations.
- [`AxiomAudit.lean`](PoolingMultiplication/AxiomAudit.lean) audits the
  transitive dependencies of every imported project declaration, including
  the supplemental counting bridges. Run the documented build and audit
  commands to verify the exact checkout being used.
