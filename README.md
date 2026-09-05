# Multiplication from two pooling principles — Lean 4

Formal verification companion to **“Multiplication from two pooling
principles”** by Eduardo Zambrano. The development uses Lean **4.24.0** and
mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; all transitive
dependency versions are pinned in [`lake-manifest.json`](lake-manifest.json).

## The question

For an operation on the positive integers, fix a requirement `a` and count
the partners that fit under capacity `N`:

\[
M_a(N)=\#\{b\geq1:a\star b\leq N\}.
\]

Two principles describe what happens when capacities are pooled:

- **Sufficiency is preserved (PS).** If `N` accommodates `b` opportunities
  and `L` accommodates `c`, then `N + L` accommodates `b + c`.
- **Insufficiency is preserved (PI).** If `N` cannot accommodate `b`
  opportunities and `L` cannot accommodate `c`, then `N + L` cannot
  accommodate `b + c`.

These axioms prescribe neither a multiplication table nor a target count.
They concern numbers of feasible partners, not prime factorizations or a
set-theoretic union of feasible sets.

## The theorem

Suppose `1` is a right identity and each row is strictly increasing.
If the operation is **commutative or associative**, then

\[
\mathrm{PS}\ \&\ \mathrm{PI}
\quad\Longleftrightarrow\quad
a\star b=ab\quad\text{for all }a,b\geq1.
\]

Associativity and commutativity need not be assumed together. Factoriality
is a **conclusion**, not a hypothesis. The theorem identifies multiplication
on the given numerical labels, not merely up to abstract isomorphism.
Ordinary addition of capacities and requested counts is part of the setup.

The main Lean declaration is
[`pooling_characterization`](PoolingMultiplication/Main.lean):

```lean
theorem pooling_characterization {op : Operation} (hpos : Positive op)
    (hunit : RightIdentity op) (hstrict : RowStrict op)
    (hcompat : Comm op ∨ Assoc op) :
    (PS op ∧ PI op) ↔ IsMultiplication op
```

Here `Positive` encodes the paper's positive-valued codomain; it is not an
additional mathematical assumption. See the translation notes below.

## Why the proof works

Strict order makes counts invertible: `M_a(N) ≥ b` exactly when
`a ⋆ b ≤ N`. The two pooling principles therefore become

\[
a\star(b+c)\leq a\star b+a\star c
\leq a\star(b+c)+1.
\]

Finite induction gives
`(a − 1)b + 1 ≤ a ⋆ b ≤ ab`. If one output were smaller than `ab`,
repeated pooling would amplify the gap. Either symmetry or associativity
then contradicts a lower bound in another row. No limit argument or
classification of individual counting functions is needed.

The rigidity core is separated from the counting bridge in
[`Rigidity.lean`](PoolingMultiplication/Rigidity.lean), so it can also be
used as a theorem about families of almost-additive integer-valued rows.

## Coverage and manuscript correspondence

The reference manuscript is the September 5, 2026 base version. The
development covers its main characterization, auxiliary equivalences and
bounds, arithmetic consequences, and all five independence/structural
examples. A declaration-level map is maintained in
[`THEOREM_MAP.md`](THEOREM_MAP.md).

| Paper result | Module |
|---|---|
| Genuine partner counts, finiteness, threshold inversion | `Counting` |
| Lemma 3.1: counting inequalities, carry, row-output intervals | `Counting`, `Supplement` |
| Lemma 3.2: the two threshold inequalities | `Counting` |
| Lemma 4.1: initial bounds and replication | `Rigidity` |
| Theorem 2.1: commutative and associative characterizations | `Main` |
| Corollary 4.2: factoriality, floor count, divisor count | `Arithmetic`, `Consequences` |
| Example 5.1: Peano operation, PS without PI | `Examples.Peano` |
| Example 5.2: odd-integer operation, PI without PS | `Examples.Odd` |
| Example 5.3: ceiling rows without compatibility | `Examples.Ceiling` |
| Remark 5.4: necessity of normalization and order | `Examples.Structural` |

In particular, the first two examples include **existence and uniqueness
of factorizations into atoms**, not merely finite computations witnessing
failed pooling. The ceiling and permutation examples are proved for all
inputs; their small numerical witnesses are exact kernel-checked proofs.

This repository does not formalize the economic motivation, claims of
novelty, or results from cited papers. The separate exploratory note about
axioms using only the aggregate factorization count is not part of this
manuscript and is not claimed as a verified result here.

## Translation and trust boundaries

- **Positive carrier.** `Operation` is implemented as `ℕ → ℕ → ℕ`.
  Structural laws and the conclusion quantify only over positive inputs.
  Values on either zero coordinate are irrelevant. Capacities may be zero.
- **Actual cardinalities.** `count` uses `Set.ncard` of the full set of
  positive feasible partners. There is no unproved count oracle or assumed
  finite cutoff. Finiteness is proved from positivity and strict order.
  For the nonmonotone XOR example, a separate finite-image argument proves
  its count; strict-order lemmas are not applied to it.
- **Arithmetic.** Natural subtraction is truncated. Bounds are often stated
  without subtraction, and the traditional positive-integer forms are
  recovered explicitly. Ceiling and half-integer formulas are implemented
  with exact integer division, never floating-point arithmetic.
- **Factoriality.** [`Factorial.lean`](PoolingMultiplication/Factorial.lean)
  states existence of a finite list of atoms and uniqueness up to
  permutation. This is the reduced positive-monoid notion used in the
  manuscript; it does not artificially adjoin a zero to use a typeclass.
- **Divisor count.** Ordered pairs are counted, including the identity in
  either position. The divisor count is `Nat.divisors.card`, obtained by an
  actual bijection, not defined to be the factorization count.

Lean checks the formal statements and their proofs. The correspondence
between these statements and the prose manuscript remains a human-readable
translation, documented in the theorem map.

## Build and audit

Install [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/eduardo-zambrano/pooling-multiplication-lean.git
cd pooling-multiplication-lean
lake exe cache get
lake build
lake env lean PoolingMultiplication/AxiomAudit.lean
```

The pinned toolchain is selected automatically. The mathlib cache avoids
rebuilding the library; the project proofs themselves are checked locally.

The source contains no proof placeholders or project-level axioms. The
audit examines the **transitive axiom dependencies of every declaration in
the project namespace**, and fails on anything outside `propext`,
`Classical.choice`, and `Quot.sound`. These are Lean's standard logical
foundations; there are no project-specific axioms or native-computation
trust extensions.

The completed local build and audit are recorded in
[`VERIFICATION.md`](VERIFICATION.md).

An optional GitHub Actions workflow is supplied at
[`ci/lean_action.yml`](ci/lean_action.yml). Automated CI is **not yet active**:
an account authorized to install workflows must place this file at
`.github/workflows/lean_action.yml`. It rebuilds the project, rejects source
placeholders and project axioms, and runs the same dependency audit. The
local verification does not depend on GitHub Actions.

## Citation and license

See [`CITATION.cff`](CITATION.cff). Until a permanent manuscript or software
identifier is available, cite the manuscript and the repository commit used.
No DOI or journal acceptance is implied.

Copyright 2026 Eduardo Zambrano. Code is released under the
[Apache License 2.0](LICENSE). The manuscript and editorial correspondence
are maintained separately and are not licensed by this repository.

OpenAI's Codex assisted with formalization and documentation. Proof
acceptance is by Lean's kernel, not by an AI-generated correctness claim.
