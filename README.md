# Knight Models

A Lean 4 / Mathlib formalization of **Knight models**, a class of structures generalizing a construction from the following paper:

Knight JF. A complete Lω1ω-sentence characterizing ℵ1. Journal of Symbolic Logic. 1977;42(1):59-62. doi:10.2307/2272318

[![CI](https://github.com/shalliso/KnightModel/actions/workflows/ci.yml/badge.svg)](https://github.com/shalliso/KnightModel/actions/workflows/ci.yml)

A Knight model is a linear order $(K, <)$ with functions $f_1, f_2, \dots$ such that for every $a \in K$, the images $f_1(a), f_2(a), \dots$ injectively enumerates $(-\infty, a]$. Any such structure is $\omega_1$-like and therefore must have cardinality at most $\aleph_1$. Knight's result is that this is tight -- such a structure of cardinality $\aleph_1$ exists.

Rather than formalizing Scott sentences and infinitary logic, we distill the notion of a Blueprint, which carries the same information as the Scott sentence. In particular, it characterizes the isomorphism class of any countable Knight model. It is a purely algebraic object: a right-cancellative monoid with additional axioms relating to right- and left-divisibility.

From a Blueprint one can derive a Knight model, and to construct a Blueprint we use a Baire category argument (in the language of forcing). To construct a Knight model of cardinality $\aleph_1$, we use Zorn's lemma.

This formalization is complete, with no `sorry` and no use of axioms other than the foundational `propext`, `Classical.choice`, and `Quot.sound`; this is confirmed by [`KnightModel/Meta/AxiomsAudit.lean`](KnightModel/Meta/AxiomsAudit.lean). A more rigorous audit with **[`leanprover/comparator`](https://github.com/leanprover/comparator)** can be done with the files in `Audit/`.

## Motivations

Rather than being a faithful formalization of an existing paper, this is an experiment in AI-assisted research in pure mathematics, using AI as a tool to automate tedious and painful case analyses in order to more quickly try ideas. The intended result is a human-authored paper appropriate for a serious journal in pure mathematics.

## Mathematical content

A **blueprint** (`Blueprint/Basic.lean`) is a countable right-cancellative monoid $\Omega$ with a compatible dense linear order and no minimum, in which $1$ is the maximum element; multiplication is order-decreasing ($a \cdot b \leq b$); if $a \leq b$ then $a = c \cdot b$ for some $c$; and if $a, b < 1$ then $a = b \cdot c$ for some $c$.

A **Knight model with blueprint $\Omega$** (`Model/Basic.lean`) is a dense linear order $\alpha$ (without endpoints) equipped with functions $f_n : \alpha \to \alpha$ for each $n \in \Omega$, satisfying: (i) $f_n(a) \leq f_m(a) \iff n \leq m$; (ii) $f_m \circ f_n = f_{m \cdot n}$; and (iii) for every $a \leq b$, the initial segment $(-\infty, b]$ equals $\{f_n(b) \mid n \in \Omega\}$.
A Knight model structure can be placed on $\{n \in \Omega \mid n < 1\}$ with $f_n(a) = n \cdot a$ (`Model/Instance.lean`).

Knight model isomorphisms and embeddings are defined in `Model/ModelIso.lean`. Every countable Knight model is ultrahomogeneous: any partial isomorphism between finitely-generated initial segments extends to a full automorphism. This is proved via a back-and-forth argument (`Model/{Condition, DenseSets, GenericFilter}.lean`).

Every Knight model has cardinality at most $\aleph_1$ (`Model/Cardinality.lean`). An uncountable Knight model of size exactly $\aleph_1$ is constructed by building an $\omega_1$-long chain of countable Knight model embeddings via Zorn's lemma and taking the colimit (`Chain/` and `Model/Aleph1.lean`).

A **knight aut group** (`KnightAutGroup/Basic.lean`) is a subgroup $K \leq \mathrm{Aut}(\mathbb{Q},
\leq)$ satisfying:

- **Transitivity**: $K$ acts transitively on $\mathbb{Q}$.
- **Fixing**: if $g \in K$ fixes $b$ and $a \leq b$, then $g$ fixes $a$.
- **Density**: for any $a < b < c$ there exists $g \in K$ fixing $a$ with $g(c) < b$.

Every knight aut group gives rise to a blueprint: the subtype $\{q \in \mathbb{Q} \mid q \leq 1\}$ with multiplication $m \cdot n = g_n(m)$, where $g_n$ is the unique group element sending $1 \mapsto n$ (`Blueprint/Instance.lean`). A knight aut group realizing any given blueprint is constructed generically: a genericity argument produces a filter through the poset of finite partial order-automorphisms of $\mathbb{Q}$, and the generated group of the resulting generic automorphisms satisfies all three axioms (`KnightAutGroup/{KnightCondition, DenseSets, GenericFilter, Instance}.lean`).

## Main results

The four public theorems are stated in [`KnightModel/MainResults.lean`](KnightModel/MainResults.lean):

| Theorem                           | Statement                                                                     |
| --------------------------------- | ----------------------------------------------------------------------------- |
| `exists_blueprint`                | A blueprint exists                                                            |
| `knightModel_card_le_aleph_one`   | Every Knight model has cardinality `#α ≤ ℵ₁`                                  |
| `exists_aleph_one_model`          | For every blueprint, there exists a Knight model with `#α = ℵ₁`               |
| `nonempty_knightIso_of_encodable` | Any two countable nonempty Knight models of the same blueprint are isomorphic |

## Building

Prerequisites: [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) and
[Lake](https://github.com/leanprover/lake).

```bash
# Clone the repository
git clone https://github.com/shalliso/KnightModel
cd KnightModel

# Fetch the Mathlib build cache (avoids recompiling Mathlib from scratch)
lake exe cache get

# Build the project
lake build
```

Always run `lake exe cache get` before `lake build` in a fresh environment.

## Repository structure

```text
KnightModel/
├── MainResults.lean         # Public theorems (start here)
├── PartialIso.lean          # partial maps API
├── Blueprint/               # Blueprint definition and instance
├── KnightAutGroup/          # KnightAutGroup definition and instance
├── Model/                   # KnightModel definition and instance 
├── Chain/                   # Zorn's lemma argument for construction of KnightModel of cardinality ℵ₁
└── Meta/                    # Checks axioms used by the public theorems

Audit/
├── README.md                # How to reproduce the comparator checks
├── Challenge.lean           # Mathlib-only theorem statements (with sorry)
├── Solution.lean            # Proofs of the challenge statements
└── comparator.json          # Comparator configuration
```

## Dependencies

| Dependency | Version          |
|------------|------------------|
| Lean 4     | `v4.28.0-rc1`    |
| Mathlib    | `v4.28.0-rc1`    |

## License

Apache 2.0 — see the [LICENSE](LICENSE) file.

## Author

Shaun Allison
