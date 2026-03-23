# Mathlib PR Plan — semicircle-catalan

A plan for extracting general-purpose lemmas and the noncrossing pairing API from this formalization into Mathlib contributions, using OpenGauss to manage the golfing and refactoring workflows.

## Overview

The formalization contains ~15 general-purpose lemmas buried among 3700+ lines of domain-specific proof. The goal is to extract, golf, and submit them as a series of small, focused Mathlib PRs.

## Current status

- [x] PR 3 groundwork: extracted `even_card_of_fpf_closed` into `SemicircleCheck/EvenCard.lean`
- [x] PR 1 groundwork: added a Mathlib-style doc comment and `@[simp]` to `finRotate_pow_apply'`
- [ ] Build-check the refactor with `lake build`
- [ ] Start the actual PR-1 extraction branch

## PR Sequence

### PR 1: `finRotate_pow_apply'` (Easiest, highest value)

**Target file:** `Mathlib.GroupTheory.Perm.Fin`

**What:** One lemma proving `(finRotate m)^k x = ⟨(x.val + k) % m, ...⟩`. Currently in `RotationArithmetic.lean`.

**Why Mathlib wants this:** Every proof involving iterated rotations on `Fin` needs this. It's the arithmetic core that `finRotate` is missing.

**Work needed:**
- Golf the proof (currently ~15 lines, should be ≤5)
- Add `@[simp]` tag
- Write doc comment
- Derive `rotate_self_eq_zero` and `rotate_succ_eq_one` as corollaries

**OpenGauss workflow:**
```
/autoprove RotationArithmetic.lean   # Golf existing proofs
```

---

### PR 2: `numCycles` — total cycle count including fixed points

**Target file:** `Mathlib.GroupTheory.Perm.Cycle.Type`

**What:**
- `numCycles σ = σ.cycleType.card + card (Function.fixedPoints σ)` — counts all orbits
- `numCycles_swap_mul_le` — multiplying by a transposition changes cycle count by at most 1
- Supporting infrastructure (~5 lemmas from GenusNoncrossing.lean's transposition-bound section)

**Why Mathlib wants this:** `cycleType.card` omitting fixed points is a known footgun. The transposition bound is useful for Cayley distance on symmetric groups.

**Work needed:**
- Extract from GenusNoncrossing.lean (currently private lemmas, need to be made public)
- Golf heavily — the transposition bound currently uses ~200 lines
- Naming conventions: follow Mathlib's `Equiv.Perm.*` pattern

**OpenGauss workflow:**
```
/autoprove GenusNoncrossing.lean     # Golf the transposition-bound section
```

---

### PR 3: `even_card_of_fpf_closed`

**Target file:** `Mathlib.GroupTheory.Perm.Support` or `Mathlib.Combinatorics.SetFamily.Basic`

**What:** A finite set closed under a fixed-point-free involution has even cardinality. Proved by strong induction: extract a pair, recurse.

**Why Mathlib wants this:** Clean combinatorial fact with applications beyond pairings.

**Work needed:**
- Extract from CatalanRecurrence.lean
- Minimal golfing needed (proof is already short)
- Find the right Mathlib home

---

### PR 4: Noncrossing pairings + Catalan counting (the main contribution)

**Target file:** New file `Mathlib.Combinatorics.Enumerative.NoncrossingPairing`

**What:**
- `IsPairing`, `Pairing n` — fixed-point-free involutions as subtype
- `Pairing.genus` — genus via cycle count
- `Pairing.IsNoncrossing` — recursive noncrossing predicate
- `Pairing.deleteAdjacent` — adjacent pair deletion
- `genus_zero_iff_noncrossing` — the bridge theorem
- `catalanEquiv` — `NCP(n+1) ≃ Σ k, NCP(k) × NCP(n-k)`
- `card_noncrossingPairing_eq_catalan` — `|NCP(n)| = Cₙ`

**Why Mathlib wants this:** Noncrossing partitions appear in free probability, Catalan combinatorics, and random matrix theory. No formalization exists in any proof assistant.

**Work needed:**
- Major golfing — GenusNoncrossing.lean (1200 lines) and CatalanRecurrence.lean (2140 lines) need significant compression
- ~50 private lemmas need review: expose ~15 as public, inline the rest
- Doc comments on all public definitions and theorems
- Depends on PRs 1–3 landing first

**OpenGauss workflow:**
```
/autoprove GenusNoncrossing.lean     # Golf bridge theorem proofs
/autoprove CatalanRecurrence.lean    # Golf Catalan decomposition
```

---

## Loading into OpenGauss

### Step 1: Initialize the project

```bash
cd ~/semicircle-catalan
gauss
/project init
```

This creates `.gauss/project.yaml` with the project manifest. Verify it detects the Lake project:

```yaml
schema_version: 1
name: "SemicircleCheck"
kind: "lean4"
lean_root: "."
```

### Step 2: Verify the build

```bash
lake build
```

Confirm 1289 jobs, 0 errors. OpenGauss needs a clean build before launching workflows.

### Step 3: Golf with autoprove

Start with the smallest file:

```
/autoprove RotationArithmetic.lean
```

Monitor progress:

```
/swarm
```

Attach to a running agent if needed:

```
/swarm attach <task-id>
```

### Step 4: Extract and reorganize

Once proofs are golfed, create a branch for each PR:

```bash
git checkout -b mathlib/finRotate-pow-apply
# Extract finRotate_pow_apply' and corollaries into standalone file
# Test with: lake build
git add -A && git commit -m "extract: finRotate_pow_apply' for Mathlib PR"
```

### Step 5: Submit

For each PR branch:

1. Fork `leanprover-community/mathlib4`
2. Add the new/modified file
3. Run `lake build` against Mathlib
4. Submit PR with description referencing this project

---

## Pre-Submission Checklist

Before any Mathlib PR:

- [ ] Post on [Lean Zulip](https://leanprover.zulipchat.com/) (#mathlib4, #new members) describing the API
- [ ] Get feedback on naming, file placement, and scope
- [ ] Every public def/theorem has a doc comment
- [ ] `@[simp]` on appropriate lemmas
- [ ] No unused imports
- [ ] Proof style follows Mathlib conventions (prefer `calc`, `simp`, tactic mode)
- [ ] CI passes on Mathlib fork

## File Inventory

Source files and what they contribute to each PR:

| Source File | Lines | PR 1 | PR 2 | PR 3 | PR 4 |
|-------------|-------|------|------|------|------|
| RotationArithmetic.lean | 152 | all | — | — | — |
| ShiftTwoEquiv.lean | 134 | — | — | — | all |
| GenusNoncrossing.lean | 1201 | — | ~200 | — | ~1000 |
| CatalanRecurrence.lean | 2139 | — | — | ~30 | ~2100 |
| Census.lean | 77 | — | — | — | — |

## Estimated Effort

| PR | Golfing | New Code | Review Cycles | Total |
|----|---------|----------|---------------|-------|
| 1: finRotate_pow_apply' | 1 day | minimal | 1–2 | ~1 week |
| 2: numCycles | 2–3 days | minimal | 2–3 | ~2 weeks |
| 3: even_card_of_fpf_closed | half day | minimal | 1 | ~1 week |
| 4: noncrossing pairings | 1–2 weeks | some restructuring | 3+ | ~1 month |

PRs 1–3 can proceed in parallel. PR 4 depends on all three.
