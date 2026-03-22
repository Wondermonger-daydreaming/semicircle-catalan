# genus-noncrossing

A Lean 4 formalization proving that **genus-zero pairings of {0, ..., 2n−1} are exactly the noncrossing pairings**, and that their count equals the Catalan number Cₙ.

## The theorem

A *pairing* of Fin(2n) is a fixed-point-free involution π. Its *genus* is defined via the cycle structure of γπ, where γ is the long cycle (finRotate). The genus is zero when γπ achieves the maximum cycle count of n + 1.

The primary result is:

```lean
theorem Pairing.genus_zero_iff_noncrossing {n : ℕ} (p : Pairing n) :
    p.genus = 0 ↔ p.IsNoncrossing
```

The counting corollary connects this to the Catalan numbers:

```lean
theorem Pairing.genus_zero_count {n : ℕ} :
    Fintype.card { p : Pairing n // p.genus = 0 } = catalan n
```

The counting proof passes through a type-level Catalan decomposition: every noncrossing pairing on 2(n+1) points decomposes uniquely into a chord target k and independent noncrossing pairings on the inside (2k points) and outside (2(n−k) points) intervals.

```lean
noncomputable def catalanEquiv (n : ℕ) :
    NoncrossingPairing (n + 1) ≃
    Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val)
```

Taking cardinalities yields the Catalan recurrence C(n+1) = Σ C(k) · C(n−k), which matches Mathlib's `catalan_succ`.

## Mathematical context

These results formalize the combinatorial core of the **Wigner semicircle law** in random matrix theory. The trace expansion of E[Tr(Wⁿ)/N] over a random Wigner matrix produces a sum over pairings, filtered by genus:

```
E[Tr(W^{2n})/N] = Σ_π N^{−2g(π)} = C_n + O(1/N²)
```

The genus-zero pairings dominate in the large-N limit. This formalization proves that these survivors are exactly the noncrossing pairings and that there are Catalan-many of them, which yields the moments of the semicircle distribution ρ(x) = (1/2π)√(4 − x²) on [−2, 2].

## Project structure

```
GenusNoncrossing/
├── GenusNoncrossing.lean       Core definitions and the bridge theorem
├── CatalanRecurrence.lean      Catalan decomposition and counting
├── ShiftTwoEquiv.lean          Coordinate deletion infrastructure
├── RotationArithmetic.lean     Rotation lemmas and group theory layer
└── Census.lean                 Small-case computational verification
```

**GenusNoncrossing.lean** (≈1200 lines) contains the definitions of `Pairing`, `IsPairing`, `IsNoncrossing`, `genus`, `numCycles`, `longCycle`, `deleteAdjacent`, `hasAdjacentAt`, and the main theorems: `genus_zero_iff_noncrossing`, `numCycles_delete_adjacent` (the cycle-splitting lemma), `maxCycles_imp
