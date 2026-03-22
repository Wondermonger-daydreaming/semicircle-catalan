# Semicircle Formalization — Handoff

*For whoever wakes next.*

---

## What This Is

A Lean 4 formalization of the combinatorial heart of the Wigner semicircle law: **genus zero ↔ noncrossing** for pairings, and the Catalan counting that follows. The theorem connects random matrix theory to enumerative combinatorics through a bridge that has been known since the 1970s but never (to our knowledge) formalized in a proof assistant.

## The Chain

```
E[Tr(W^{2n})/N] → trace expansion → pairing sum → genus filter
→ genus 0 = noncrossing = Catalan → semicircle moments
```

We are formalizing the middle link: **genus 0 ↔ noncrossing ↔ Catalan count**.

## Project Structure

```
semicircle-catalan/
├── src/
│   ├── GenusNoncrossing.lean       — Core definitions + bridge theorem (current)
│   └── GenusNoncrossing_sketch.lean — Original sketch / early blueprint
├── assets/                         — Visualizations (PNGs, GIFs, React explorer)
├── notes/                          — Session diary, stimulus questions, fragments
├── HANDOFF.md                      — This file
├── README.md
└── LICENSE
```

The intended modular decomposition (ShiftTwoEquiv, RotationArithmetic, CatalanRecurrence, Census) currently lives in `src/GenusNoncrossing.lean` as a monolithic blueprint. Splitting into separate files is a future step.

## Build

```bash
lake build    # ~2 min with Mathlib cache
```

## What's Proved (no sorry)

### ShiftTwoEquiv.lean — FULLY SORRY-FREE
- `shiftTwoEquiv`: Fin(2n) ≃ {x : Fin(2n+2) | x ≥ 2}
- `mapsTo_remaining`: π(0)=1 ∧ π(1)=0 → π maps {x≥2} to {x≥2}
- `symm_mapsTo_remaining`: same for π⁻¹
- `contractZeroOne`: restrict π to {x≥2}, conjugate through shiftTwoEquiv
- `contractZeroOne_isPairing`: conjugation preserves involution + FPF

### RotationArithmetic.lean
- `rotate_self_eq_zero`: finRotate^(m-i) sends i to 0
- `inv_apply_of_apply`: ρ(a)=b → ρ⁻¹(b)=a (pure injectivity)
- `involution_reverse`: π²=1 ∧ π(i)=j → π(j)=i
- `conjugate_sends`: rotation + adjacency → conjugate sends a↦b
- `conjugate_sends_back`: same via involution for reverse direction

### CatalanRecurrence.lean
- `insideEquiv`: Fin(2k) ≃ {i | 0 < i < 2k+1}
- `outsideEquiv`: Fin(2(n-k)) ≃ {i | 2k+1 < i}
- `even_card_of_fpf_closed`: **THE COMBINATORIAL LEDGER** — closed FPF-involution sets have even cardinality (strong induction, extract pair, recurse)
- `shadow_closed_of_no_crossing`: **THE QUARANTINE** — if no crossings, shadow {1,...,p(0)-1} is closed under p
- `noncrossing_mapsTo_shadow`: quarantine composed with bridge direction
- Shadow cardinality = t-1 via Fin(t-1) ↪ Fin(2(n+1))
- Parity wiring: Odd(t-1), Even demanded by ledger, absurd

### GenusNoncrossing.lean
- `longCycle_isCycle`: finRotate is a single cycle
- `Fintype (Pairing n)`, `DecidablePred IsPairing`

### Census.lean
- Small-case verification via `decide` (n=1,2 pairings)
- Python census confirms Harer-Zagier table through n=6

## What's Sorry'd (the frontier)

### Easy (routine, should fall quickly)
| Lemma | File | Notes |
|-------|------|-------|
| `finRotate_pow_apply'` | RotationArithmetic | Induction on k, `Nat.add_mod` |
| `rotate_succ_eq_one` | RotationArithmetic | finRotate value + omega |

### Medium (combinatorial arguments)
| Lemma | File | Notes |
|-------|------|-------|
| `IsNoncrossing_imp_no_crossing` | CatalanRecurrence | **Unlocks parity theorem.** Induction: bumps of length 1 can't interleave, remaining arcs biject with p' |
| `no_crossing_imp_IsNoncrossing` | CatalanRecurrence | Existence of adjacent pairs in crossing-free pairings |
| `numCycles_eq_num_orbits` | GenusNoncrossing | Bookkeeping: cycleType.card + fixedPoints = orbits |
| `Pairing.numCycles_le` | GenusNoncrossing | Upper bound n+1 on cycle count for pairings |
| `Pairing.genus_exact` | GenusNoncrossing | Parity of n+1 - numCycles |

### Hard (deep combinatorial content)
| Lemma | File | Notes |
|-------|------|-------|
| `numCycles_delete_adjacent` | GenusNoncrossing | **THE CYCLE-SPLITTING LEMMA.** Removing adjacent pair increases cycle count by 1. Orbit analysis. |
| `maxCycles_imp_noncrossing` | GenusNoncrossing | Stage B: crossing → cycle merger (contrapositive) |
| `noncrossing_imp_maxCycles` | GenusNoncrossing | Stage C: induction via deletion + splitting |
| `catalanEquiv` | CatalanRecurrence | Full Catalan bijection NCP(n+1) ≃ Σ k, NCP(k) × NCP(n-k) |

## Key Definitions

```lean
-- A pairing is a fixed-point-free involution
def IsPairing {n : ℕ} (π : Perm (Fin (2 * n))) : Prop :=
  π ^ 2 = 1 ∧ ∀ x, π x ≠ x

-- Subtype of pairings
def Pairing (n : ℕ) := { π : Perm (Fin (2 * n)) // IsPairing π }

-- Genus via cycle count of γπ
def Pairing.genus (p : Pairing n) : ℕ :=
  ((n + 1) - numCycles (longCycle n * p.val)) / 2

-- Adjacent pair: π(i) = i+1 mod 2n
def Pairing.hasAdjacentAt (p : Pairing n) (i : Fin (2 * n)) : Prop :=
  p.val i = finRotate (2 * n) i

-- Recursive noncrossing: peel adjacent pairs
def Pairing.IsNoncrossing : {n : ℕ} → Pairing n → Prop
  | 0, _ => True
  | n + 1, p => ∃ i, ∃ h : p.hasAdjacentAt i, (p.deleteAdjacent i h).IsNoncrossing

-- Arc-based crossing
def Pairing.HasCrossing (p : Pairing n) : Prop :=
  ∃ a b, a.val < b.val ∧ b.val < (p.val a).val ∧ (p.val a).val < (p.val b).val
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
-- or use directly: have h := p.property.1
```

### Doc Comments Must Precede Declarations
`/-! ... -/` before `import` = parse error. Imports must come first.

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

## Next Steps (Recommended Priority)

1. **`finRotate_pow_apply'`** — Easy win. Induction on k. Closes the rotation arithmetic.
2. **`IsNoncrossing_imp_no_crossing`** — Medium. Unlocks the parity theorem completely. Bumps of length 1 can't interleave.
3. **`numCycles_delete_adjacent`** — Hard. The cycle-splitting lemma. Orbit analysis of γπ when an adjacent pair is removed.
4. **`catalanEquiv`** — The summit. Needs the parity theorem + interval restrictions + gluing.

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
