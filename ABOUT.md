# About semicircle-catalan

`semicircle-catalan` is a Lean 4 formalization of the finite combinatorics behind the genus-zero term in the Wigner semicircle law.

The repository proves that pairings of `Fin (2 * n)` with genus zero are exactly the noncrossing pairings, and that they are counted by the Catalan number `catalan n`.

## The theorem in one paragraph

A pairing is represented as a fixed-point-free involution `π` on `Fin (2 * n)`. Let `γ` be the long cycle, implemented by Mathlib's `finRotate`. The total cycle count `Equiv.Perm.numCycles (γ * π)` determines a genus. The formalization proves that the maximum-cycle, genus-zero case is equivalent to the recursive noncrossing condition obtained by repeatedly deleting adjacent paired vertices. It then decomposes noncrossing pairings by the partner of `0`, giving the Catalan recurrence.

## What is formalized

- Pairings as fixed-point-free involutions on `Fin (2 * n)`.
- A total cycle-count API for permutations, including fixed points.
- The genus of a pairing via the long cycle `γ` and pairing involution `π`.
- A recursive noncrossing predicate based on deleting adjacent pairs.
- Rotation-normalized deletion infrastructure for adjacent pairs.
- The bridge theorem: genus zero if and only if noncrossing.
- A Catalan decomposition equivalence for noncrossing pairings.
- The final cardinality theorem: genus-zero pairings are counted by `catalan n`.

## Main Lean entry points

- `Pairing n`: pairings on `2n` points.
- `Pairing.genus`: genus computed from the cycle count of `γπ`.
- `Pairing.IsNoncrossing`: recursive noncrossing predicate.
- `Pairing.genus_zero_iff_noncrossing`: genus-zero/noncrossing equivalence.
- `catalanEquiv`: decomposition of `NCP(n+1)` into `Σ k, NCP(k) × NCP(n-k)`.
- `card_noncrossingPairing_eq_catalan`: `Fintype.card (NoncrossingPairing n) = catalan n`.
- `Pairing.genus_zero_count`: the genus-zero counting corollary.

## Proof architecture

The formalization is split into four layers:

1. Finite-index bookkeeping: equivalences and rotation lemmas for reindexing `Fin` after deleting adjacent vertices.
2. Pairing infrastructure: fixed-point-free involutions, adjacent-pair deletion, and the recursive noncrossing predicate.
3. Genus bridge: cycle-count lemmas showing that adjacent-pair deletion changes the cycle count of `γπ` in the expected way.
4. Catalan counting: a decomposition by the partner of vertex `0`, giving the Catalan recurrence and final cardinality theorem.

The proof uses rotation normalization heavily: an arbitrary adjacent pair is rotated to the boundary case `(0, 1)`, handled there, and transported back by conjugation.

## Why this matters

In the trace-moment expansion for Wigner random matrices, pairings contribute according to their genus. In the large-`N` limit, only genus-zero pairings survive. Classically, these are exactly the noncrossing pairings, whose count is the Catalan number.

This project formalizes that discrete combinatorial core. It does not formalize the analytic probability theory of the semicircle law, matrix expectations, or weak convergence.

## Mathlib extraction path

Several components are isolated for possible Mathlib contributions:

- `SemicircleCheck/FinRotateLemmas.lean`: arithmetic lemmas for powers of `finRotate`.
- `SemicircleCheck/EvenCard.lean`: finite sets closed under fixed-point-free involutions have even cardinality.
- Cycle-count infrastructure from `GenusNoncrossing.lean`.
- Noncrossing-pairing and Catalan-counting infrastructure from `CatalanRecurrence.lean`.

The extraction plan is tracked in `MATHLIB_PR_PLAN.md`; the first prepared submission package is `PR1_SUBMISSION.md`.

## Build target

The Lake target is `SemicircleCheck`.

```bash
lake exe cache get
lake build
```

The checked toolchain is recorded in `lean-toolchain`.
