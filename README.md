# semicircle-catalan

A Lean 4 formalization of the genus-zero/noncrossing-pairing theorem behind the Catalan moments in the Wigner semicircle law.

The core result: for pairings of `Fin (2 * n)`, the genus-zero condition defined from the total cycle count `Equiv.Perm.numCycles (γ * π)` is equivalent to noncrossing, and the number of such pairings is the Catalan number `C_n`.

For a plain-language overview, see [`ABOUT.md`](ABOUT.md). For the planned Mathlib extraction sequence, see [`MATHLIB_PR_PLAN.md`](MATHLIB_PR_PLAN.md).

## Status

- Sorry-free: no `sorry` or `admit` in the project sources.
- Checked against Lean `v4.29.0-rc6` and Mathlib with `lake build`.
- Main Lake target: `SemicircleCheck`.
- Current repo work: formalization is complete; extraction/golfing for Mathlib PRs is being staged.

## Main results

| Lean name | Informal statement |
|----------|--------------------|
| `Pairing.genus_zero_iff_noncrossing` | A pairing has genus zero iff it is noncrossing. |
| `catalanEquiv` | `NCP(n+1) ≃ Σ k, NCP(k) × NCP(n-k)`. |
| `card_noncrossingPairing_eq_catalan` | The number of noncrossing pairings on `2n` points is `catalan n`. |
| `Pairing.genus_zero_count` | The number of genus-zero pairings is `catalan n`. |

The Catalan equivalence decomposes a noncrossing pairing by the partner of vertex `0`. If `0` is paired with `2k+1`, the remaining vertices split into independent inside and outside noncrossing pairings of sizes `2k` and `2(n-k)`.

## Core definitions

A pairing is a fixed-point-free involution:

```lean
def IsPairing {n : ℕ} (π : Perm (Fin (2 * n))) : Prop :=
  π ^ 2 = 1 ∧ ∀ x, π x ≠ x

def Pairing (n : ℕ) := { π : Perm (Fin (2 * n)) // IsPairing π }
```

The long cycle `γ` is Mathlib's `finRotate`. The genus of a pairing is computed from `Equiv.Perm.numCycles (γ * π)`, a total cycle count including fixed points.

Noncrossing is defined recursively: a pairing is noncrossing if it can be reduced to the empty pairing by repeatedly deleting adjacent paired vertices.

## Build

```bash
lake exe cache get   # optional, recommended
lake build
```

The root import is [`SemicircleCheck.lean`](SemicircleCheck.lean), which imports every project module.

## Project structure

```text
semicircle-catalan/
├── SemicircleCheck/
│   ├── ShiftTwoEquiv.lean        # Fin reindexing for deletion
│   ├── FinRotateLemmas.lean      # finRotate arithmetic lemmas
│   ├── RotationArithmetic.lean   # rotation normalization
│   ├── GenusNoncrossing.lean     # definitions + genus/noncrossing bridge
│   ├── EvenCard.lean             # finite FPF-involution parity lemma
│   ├── CatalanRecurrence.lean    # Catalan decomposition + counting theorem
│   └── Census.lean               # small-n computational reference data
├── SemicircleCheck.lean          # library root
├── ABOUT.md                      # project overview
├── MATHLIB_PR_PLAN.md            # Mathlib extraction plan
├── PR1_SUBMISSION.md             # prepared finRotate PR package
├── PR1_FINROTATE_STANDALONE_PATCH.lean
├── lakefile.toml
├── lean-toolchain
└── LICENSE
```

Dependency sketch:

```text
ShiftTwoEquiv ──→ GenusNoncrossing ──→ CatalanRecurrence
FinRotateLemmas ─→ RotationArithmetic ─┘
EvenCard ────────────────────────────┘
```

## Computational reference

A small census, recorded in [`SemicircleCheck/Census.lean`](SemicircleCheck/Census.lean), matches the Catalan genus-zero counts:

| `2n` | Total pairings | Genus zero | `C_n` |
|-----:|---------------:|-----------:|------:|
| 2 | 1 | 1 | 1 |
| 4 | 3 | 2 | 2 |
| 6 | 15 | 5 | 5 |
| 8 | 105 | 14 | 14 |
| 10 | 945 | 42 | 42 |
| 12 | 10,395 | 132 | 132 |

## Mathlib extraction status

The project contains several pieces intended to be extractable into Mathlib:

- `finRotate` power formulas from `FinRotateLemmas.lean`; see [`PR1_SUBMISSION.md`](PR1_SUBMISSION.md) and [`PR1_FINROTATE_STANDALONE_PATCH.lean`](PR1_FINROTATE_STANDALONE_PATCH.lean).
- `even_card_of_fpf_closed` from `EvenCard.lean`.
- `Equiv.Perm.numCycles`, a total cycle-count API for permutations including fixed points.
- The noncrossing pairing API and Catalan counting theorem.

The planned sequence is tracked in [`MATHLIB_PR_PLAN.md`](MATHLIB_PR_PLAN.md).

## Mathematical context

In the trace-moment expansion for Wigner random matrices, pairings contribute with a power determined by genus. In the large-`N` limit, only genus-zero pairings survive. These are exactly the noncrossing pairings, and their count gives the Catalan moment sequence of the semicircle distribution.

This repository formalizes that finite combinatorial core. It does not formalize the analytic probability theory of the semicircle law.

## License

Apache 2.0. See [`LICENSE`](LICENSE).

## Acknowledgments

This formalization was developed with Lean 4 and Mathlib, using OpenGauss-managed proving workflows for project orchestration and proof search.
