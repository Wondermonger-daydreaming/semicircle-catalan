# semicircle-catalan

**A Lean 4 formalization of the genus-zero characterization of noncrossing pairings and the Catalan counting theorem.**

For pairings of $\text{Fin}(2n)$, the composition $\gamma\pi$ of the long cycle $\gamma$ with the pairing involution $\pi$ achieves its maximum cycle count if and only if $\pi$ is noncrossing. The genus-zero condition is a corollary, and the number of such pairings equals the Catalan number $C_n$.

## Status

**Sorry-free.** All definitions and theorems compile without `sorry` against Lean 4.29.0-rc6 and Mathlib (1289 jobs, ~2 min with cache).

## Core definitions

A **pairing** of $\{0, \ldots, 2n-1\}$ is a fixed-point-free involution:

```lean
def IsPairing {n : ℕ} (π : Perm (Fin (2 * n))) : Prop :=
  π ^ 2 = 1 ∧ ∀ x, π x ≠ x

def Pairing (n : ℕ) := { π : Perm (Fin (2 * n)) // IsPairing π }
```

The **long cycle** $\gamma$ sends $i \mapsto i + 1 \bmod 2n$, implemented as Mathlib's `finRotate`. The **genus** of a pairing is defined via the total cycle count of $\gamma\pi$:

```lean
def Pairing.genus (p : Pairing n) : ℕ :=
  ((n + 1) - numCycles (longCycle n * p.val)) / 2
```

where `numCycles` counts all orbits (nontrivial cycles and fixed points), correcting for the fact that Mathlib's `cycleType.card` omits fixed points.

A pairing is **noncrossing** if it can be reduced to the empty pairing by iteratively removing adjacent pairs ($\pi(i) = i + 1 \bmod 2n$):

```lean
def Pairing.IsNoncrossing : {n : ℕ} → Pairing n → Prop
  | 0, _ => True
  | n + 1, p => ∃ i, ∃ h : p.hasAdjacentAt i, (p.deleteAdjacent i h).IsNoncrossing
```

## Main results

| Theorem | Statement |
|---------|-----------|
| `genus_zero_iff_noncrossing` | $\text{genus}(\pi) = 0 \iff \pi \text{ is noncrossing}$ |
| `catalanEquiv` | $\text{NCP}(n+1) \simeq \sum_{k=0}^{n} \text{NCP}(k) \times \text{NCP}(n-k)$ |
| `card_noncrossingPairing_eq_catalan` | $\lvert\text{NCP}(n)\rvert = C_n$ |
| `Pairing.genus_zero_count` | $\lvert\{p : \text{Pairing}(n) \mid \text{genus}(p) = 0\}\rvert = C_n$ |

The bridge theorem `genus_zero_iff_noncrossing` connects the topological condition (genus zero) with the combinatorial condition (noncrossing). It is proved in two stages:

- **Noncrossing $\Rightarrow$ max cycles**: induction on the recursive noncrossing predicate, using a cycle-splitting lemma that shows deleting an adjacent pair increases the cycle count of $\gamma\pi$ by exactly one.
- **Max cycles $\Rightarrow$ noncrossing**: contrapositive argument via the existence of crossings when the cycle count is submaximal.

The Catalan equivalence `catalanEquiv` is a type-level bijection: vertex 0 pairs with some odd vertex $2k+1$ (the parity theorem), partitioning the remaining $2n$ vertices into independent noncrossing domains of sizes $2k$ and $2(n-k)$. Taking cardinalities recovers the Catalan recurrence $C_{n+1} = \sum_{k=0}^{n} C_k \, C_{n-k}$.

## Project structure

```
semicircle-catalan/
├── SemicircleCheck/
│   ├── ShiftTwoEquiv.lean        — Fin reindexing (deletion infrastructure)
│   ├── RotationArithmetic.lean   — finRotate arithmetic + group theory layer
│   ├── GenusNoncrossing.lean     — Core definitions, genus bridge theorem
│   ├── CatalanRecurrence.lean    — Catalan decomposition + counting theorem
│   └── Census.lean               — Computational verification for small n
├── SemicircleCheck.lean          — Library root
├── lakefile.toml                 — Lake build configuration
├── lean-toolchain                — Lean 4.29.0-rc6
├── lake-manifest.json            — Dependency lock
├── README.md
└── LICENSE
```

**Dependency graph:**

```
ShiftTwoEquiv ──→ GenusNoncrossing ──→ CatalanRecurrence
RotationArithmetic ─┘
```

## Build

Requires [Lean 4](https://leanprover.github.io/) (v4.29.0-rc6) and [Mathlib](https://leanprover-community.github.io/mathlib4/).

```bash
lake build       # 1289 jobs, ~2 min with Mathlib cache
```

### Mathlib dependencies

- `Mathlib.Combinatorics.Enumerative.Catalan` — `catalan`, `catalan_succ`
- `Mathlib.GroupTheory.Perm.Fin` — `finRotate`, `isCycle_finRotate`
- `Mathlib.GroupTheory.Perm.Cycle.Type` — `cycleType`, cycle structure
- `Mathlib.GroupTheory.Perm.Basic` — `Equiv.Perm` algebra
- `Mathlib.Data.Fin.Basic` — `Fin` arithmetic

## Mathematical context

The results formalized here constitute the combinatorial core of the **Wigner semicircle law** in random matrix theory. The trace expansion of a Wigner matrix decomposes into a sum over pairings, weighted by genus:

$$\mathbb{E}\left[\frac{1}{N}\text{Tr}(W^{2n})\right] = \sum_{\pi \in \text{Pairings}(2n)} N^{-2g(\pi)}$$

In the large-$N$ limit, only genus-zero pairings survive. These are exactly the noncrossing pairings, and their count $C_n$ gives the $2n$-th moment of the semicircle distribution $\rho(x) = \frac{1}{2\pi}\sqrt{4 - x^2}$ on $[-2, 2]$.

This formalization proves the combinatorial link — genus zero $\Leftrightarrow$ noncrossing $\Leftrightarrow$ Catalan count — without formalizing the analytic components (measure theory, weak convergence, matrix expectations).

### Computational verification

A Python census exhaustively enumerates all pairings through $2n = 12$ and verifies:

| $2n$ | Total pairings | Genus 0 | $C_n$ |
|------|----------------|---------|-------|
| 2 | 1 | 1 | 1 |
| 4 | 3 | 2 | 2 |
| 6 | 15 | 5 | 5 |
| 8 | 105 | 14 | 14 |
| 10 | 945 | 42 | 42 |
| 12 | 10,395 | 132 | 132 |

The genus distribution follows the Harer-Zagier numbers. At 12 points, genus-2 pairings (6,468) outnumber genus-1 (2,310). The noncrossing pairings are a vanishing minority: 132 sphere-makers among 10,395.

## Design decisions

- **`Pairing n` as subtype.** Carrying proof terms through definitions creates fragmentation where `⟨0, proof₁⟩` and `⟨0, proof₂⟩` are syntactically distinct. The subtype bundles the proof once.

- **`numCycles` includes fixed points.** Mathlib's `cycleType.card` counts only nontrivial cycles (length $\geq 2$). The genus formula requires all orbits. Using `cycleType.card` alone produces incorrect genera — a genus-0 pairing would be misclassified as genus 2.

- **Recursive noncrossing predicate.** The arc-crossing definition ($\exists\, a < b < \pi(a) < \pi(b)$) is intuitive but hard to induct on. The recursive definition (peel adjacent pairs) aligns with the Catalan recursion and the `deleteAdjacent` machinery. An equivalence between the two definitions is proved as part of the bridge infrastructure.

- **Rotation normalization.** All adjacent pair deletions are normalized to $(0, 1)$ by conjugating with a power of `finRotate`. This reduces the deletion machinery to a single case (handled by `contractZeroOne`), with cyclic symmetry doing the rest.

## References

- E. P. Wigner, *Characteristic vectors of bordered matrices with infinite dimensions*, Ann. of Math. **62** (1955), 548–564.
- J. Harer and D. Zagier, *The Euler characteristic of the moduli space of curves*, Invent. Math. **85** (1986), 457–485.
- R. Speicher, *Free probability and random matrices*, Proceedings of the ICM (2014).
- B. Nica and R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University Press, 2006.
- The [Mathlib](https://leanprover-community.github.io/mathlib4/) library for Lean 4.

## Acknowledgments

This formalization project was built using [OpenGauss](https://github.com/math-inc/OpenGauss) by [Math, Inc.](https://www.math.inc/), a project-scoped Lean workflow orchestrator that provides a multi-agent frontend for the `lean4-skills` proving, drafting, and autoformalization workflows developed by Cameron Freer.

OpenGauss handled project management, managed backend setup, workflow spawning, swarm tracking, and recovery throughout the formalization process. Its `autoprove` and `sorry-filler-deep` workflows, backed by Claude Code (Anthropic's Claude Opus 4.6), were responsible for filling the majority of proof obligations across `RotationArithmetic.lean`, `GenusNoncrossing.lean`, and `CatalanRecurrence.lean`.

Several results in this project were discovered or corrected by the autoprove agent during formalization, including a boundary condition error at n=0 affecting three theorem statements, and a sign-based parity proof for the genus formula assembled from Mathlib's permutation group infrastructure.

OpenGauss was developed with support from DARPA's expMath (Exponentiating Mathematics) program and launched at the expMath kickoff. We are grateful to the Math, Inc. team for making it openly available.

We also acknowledge:

- The [Lean](https://lean-lang.org/) theorem prover and the [Lean FRO](https://lean-lang.org/fro/about/)
- [Mathlib](https://leanprover-community.github.io/), the community-driven mathematical library for Lean 4
- [Anthropic](https://www.anthropic.com/) for Claude Code and Claude Opus 4.6

## License

Apache 2.0
