# Verification record

## Local verification — September 6, 2026

Toolchain: `leanprover/lean4:v4.24.0`.

Mathlib: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`, with all transitive
dependencies recorded in `lake-manifest.json`.

Commands completed successfully:

```sh
lake build
lake env lean PoolingMultiplication/AxiomAudit.lean
```

Final build: **7,364 successful jobs**, including cached library targets;
this is a build-job count, not a theorem count. No project warnings remained.

Audit result:

```text
Audited 306 project declarations: only propext, Classical.choice, Quot.sound.
```

The audit traverses the transitive dependencies of all declarations in the
`PoolingMultiplication` namespace, including definitions and generated
auxiliary declarations. It fails on any axiom outside the three standard
foundations above. In particular, the main characterization, both separate
rigidity arguments, the factoriality and divisor-count results, and all
counterexamples have no additional trusted assumptions.

The count includes generated declarations: **306 is not advertised as 306
independent mathematical theorems**. The human-facing results are listed in
[`THEOREM_MAP.md`](THEOREM_MAP.md).

## Reproducibility

The local build reused an already installed mathlib cache. No local path is
part of the committed dependency specification, and no other manuscript's
Lean source is imported. On another machine, `lake exe cache get` obtains
the matching library cache before `lake build` checks this project.

The workflow at `.github/workflows/lean_action.yml` performs an independent
Linux build with the pinned toolchain and dependencies, source placeholder
checks, and the same dependency audit. It was activated on September 6,
2026 (in the tagged v1.0.0 sources it existed only as the uninstalled
template `ci/lean_action.yml`). Remote run outcomes are recorded on the
repository's Actions page; this file claims only the local results above.

## Scope

The audit validates the formal proofs, not novelty, journal suitability, or
the economic interpretations. The declaration map documents the translation
from the manuscript's positive integers to Lean's natural-number encoding.
No paper hypothesis is silently replaced by a multiplication comparison or
a unique-factorization assumption.
