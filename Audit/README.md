# Comparator Audit

This directory contains Mathlib-only comparator challenges for the four public theorems
in [`KnightModel/MainResults.lean`](../KnightModel/MainResults.lean).

## What is checked

Each of the four theorems is restated in `Challenge.lean` using **only Mathlib** — no
project definitions. `Solution.lean` proves those exact statements by importing the full
KnightModel library and bridging the parallel class definitions. The
[`leanprover/comparator`](https://github.com/leanprover/comparator) tool confirms that the
challenge and solution have identical elaborated types and that the proofs use only the
three standard axioms.

| Theorem | Statement |
| --- | --- |
| `exists_blueprint` | A blueprint exists (the abstract axiomatization is non-vacuous) |
| `knightModel_card_le_aleph_one` | Every Knight model has cardinality `#α ≤ ℵ₁` |
| `exists_aleph_one_model` | For every blueprint, there exists a Knight model with `#α = ℵ₁` |
| `nonempty_knightIso_of_encodable` | Any two countable nonempty Knight models of the same blueprint are isomorphic |

## Reproducing the check

Build the challenge and solution:

```bash
lake build Audit.Challenge Audit.Solution
```

Run the comparator (from the KnightModel project root):

```bash
lake env comparator Audit/comparator.json
```

Expected output (last lines):

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

## Tool versions

| Tool | Version |
| --- | --- |
| Lean / Mathlib | `v4.28.0-rc1` |
| comparator | commit `1b82ba006811f7e25d53858252372e4d85fd3921` |
| lean4export | commit `3de59f10bc4b4a0f2de698597aeb1246caa0df0a` |

