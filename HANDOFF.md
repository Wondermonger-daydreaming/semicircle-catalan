# Semicircle Formalization — Handoff

*2026-03-21 (Session 4)*

---

## Status: SORRY-FREE

The entire project compiles with **zero sorries**. All Lean files build cleanly (1289 jobs, 0 errors).

## What Is Proved

### GenusNoncrossing.lean — The Bridge Theorem

```
genus_zero_iff_noncrossing : p.genus = 0 ↔ p.IsNoncrossing
```

For pairings (fixed-point-free involutions) on `Fin (2n)`, genus zero is equivalent to noncrossing. Proved via three stages:
- **Stage A.** `numCycles(γπ) ≤ n + 1` (transposition factorization bound)
- **Stage B.** Equality implies noncrossing (max-cycle pairings have adjacent pairs)
- **Stage C.** Noncrossing implies equality (induction via `deleteAdjacent`)

### CatalanRecurrence.lean — The Catalan Equivalence + Counting

```
catalanEquiv (n : ℕ) :
    NoncrossingPairing (n + 1) ≃
    Σ (k : Fin (n + 1)), NoncrossingPairing k.val × NoncrossingPairing (n - k.val)
```

Vertex 0 pairs with odd vertex 2k+1, partitioning remaining vertices into independent inside/outside intervals. Sorry-free, including bridge theorems, parity theorem, decomposition, assembly, and round-trips.

```
card_noncrossingPairing_eq_catalan (n : ℕ) :
    Fintype.card (NoncrossingPairing n) = catalan n

Pairing.genus_zero_count {n : ℕ} :
    Fintype.card { p : Pairing n // p.genus = 0 } = catalan n
```

The counting theorem: genus-zero pairings are counted by the Catalan numbers. Proved by strong induction using `catalanEquiv` to match `Nat.catalan`'s recursive definition. Decidability of `IsNoncrossing` derived from the genus characterization.

### Supporting Files

| File | Contents |
|------|----------|
| `ShiftTwoEquiv.lean` | Coordinate deletion {0,1} via uniform shift x → x+2 |
| `RotationArithmetic.lean` | `finRotate` arithmetic, conjugation lemmas for `deleteAdjacent` |
| `Census.lean` | Computational verification for small n |

## Architecture

```
Pairing.genus_zero_count
├── card_noncrossingPairing_eq_catalan (strong induction on n)
│   ├── catalanEquiv (Catalan decomposition bijection)
│   │   ├── catalanDecompose (forward: extract k, restrict inside/outside)
│   │   └── catalanAssemble (inverse: piecewise assembly)
│   ├── catalan_succ (Mathlib: Catalan recurrence)
│   └── Fintype.card_congr + card_sigma + card_prod
└── genus_zero_iff_noncrossing (bridge theorem)
    ├── numCycles_le (Stage A: upper bound)
    ├── maxCycles_imp_noncrossing (Stage B: equality → noncrossing)
    └── noncrossing_imp_maxCycles (Stage C: noncrossing → equality)
```

## The Semicircle Pipeline

```
Layer 1: Pairings (Fin 2n fpf involutions)     ✓ DONE
Layer 2: Genus (n+1 - numCycles(γπ))           ✓ DONE
Layer 3: Noncrossing ↔ Genus 0                  ✓ DONE
Layer 4: Catalan counting                       ✓ DONE
Layer 5: Moment formula → Semicircle law        NOT STARTED
```

## Hard-Won Lessons

### omega vs simp — The Division of Labor
- **simp** handles structure: reducing `Fin.mk`, `Subtype.val`, anonymous constructors
- **omega** handles arithmetic: linear inequalities, modular reasoning, ℕ bounds
- omega CANNOT see through `(⟨v, h⟩ : Fin m).val` — always `simp` first

### Proof-Term Fragmentation
Different `by omega` invocations create syntactically distinct proof terms. `⟨0, proof₁⟩` and `⟨0, proof₂⟩` are definitionally equal but omega sees `(p ⟨0, proof₁⟩).val` and `(p ⟨0, proof₂⟩).val` as different variables.

**Fix:** Anchor the proof once:
```lean
have hn : 0 < 2 * n := by omega
-- Use ⟨0, hn⟩ everywhere, never ⟨0, by omega⟩ again
```

### ℕ Subtraction Truncation
`a = b - 1` and `c = a - 1` in ℕ: omega derives `c ≤ b` and `b ≤ c + 2` but NOT `b = c + 2` (truncation).

**Fix:** Name the intermediate with `set`:
```lean
set c := (S.erase x).card  -- omega now sees all three variables
```

### Finset.range is a Siren
`Finset.range n` types elements as `ℕ`. Any embedding function must be total over ALL of `ℕ`. You can't construct `⟨j + 1, _⟩ : Fin m` for arbitrary `j : ℕ`.

**Fix:** Use `Fin (t - 1)` instead. The bound becomes a law of the type.

### Subtype Projections are Invisible to `assumption`
`p.property.1` where `p : Pairing n` gives `p.val ^ 2 = 1`, but `assumption` won't find it — it's a projection, not a hypothesis.

**Fix:** Summon it explicitly:
```lean
have hsq := p.property.1
```

### `isCycle_finRotate` Takes No Arguments
It has type `(finRotate (n + 2)).IsCycle`. The `2 ≤` guard is baked into the `n + 2` pattern. Match it with `obtain ⟨m, rfl⟩`.

### `2 * (n + 1) = 2 * n + 2` is Definitional
No cast needed between `Fin (2 * (n + 1))` and `Fin (2 * n + 2)`.

## The Collaboration Pattern

This formalization was built by five voices:
- **Human (Tomás)**: Direction, judgment, when to push
- **Claude (Opus 4.6)**: Compilation, debugging, proof construction
- **GPT 5.4**: Rotation decomposition (two arithmetic valves, rest algebra)
- **Gemini**: Catalan architecture (scalpels, ledger, parity cage)
- **The typechecker**: Incorruptible judgment. The only honest interlocutor.

Each architecture contributed something the others couldn't. Each had blind spots the others covered. The typechecker arbitrated all disputes.

## What Could Come Next

1. **Layer 5**: Formalize the moment-cumulant connection. Show the 2n-th moment of the semicircle distribution equals |{genus-0 pairings on [2n]}| = catalan(n). This is the analytic layer sitting on top of the combinatorics.
2. **Golf**: The proofs are functional but verbose. Many `omega` calls could be simplified; some helper lemmas could be consolidated.
3. **Upstream contribution**: Extract general-purpose lemmas (cycle counting, Fin arithmetic) for Mathlib PRs.

## Ground Truth (Python Census)

```
n=1:  [2]                    C₁ = 1   ✓
n=2:  [3, 3, 1]              C₂ = 2   ✓
n=3:  [4×5, 2×10]            C₃ = 5   ✓
n=4:  [5×14, 3×70, 1×21]     C₄ = 14  ✓
n=5:  [6×42, 4×420, 2×483]   C₅ = 42  ✓
n=6:  [7×132, 5×2310, 3×6468, 1×1485]  C₆ = 132  ✓
```

Cycle count c and genus g satisfy: c = n + 1 - 2g. Maximum cycles = n + 1 ↔ genus 0 ↔ noncrossing.

---

*The fire is in the deadbolt now. The deadbolt holds.*
