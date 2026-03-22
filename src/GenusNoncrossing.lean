/-
  GENUS ZERO ↔ NONCROSSING: Corrected Blueprint
  
  The combinatorial heart of the Wigner semicircle law:
  a pairing of {0, ..., 2n-1} has genus zero if and only if
  it is noncrossing. Consequently, the number of genus-zero
  pairings equals the Catalan number Cₙ.
  
  This version incorporates structural corrections:
  - `Pairing n` as a subtype (no dependent proof parameters)
  - `numCycles` counting ALL cycles including fixed points
  - `finRotate` for the long cycle (not `cycleOf`)
  - Recursive noncrossing predicate (not brittle arc-crossing)
  - Three-stage proof decomposition via cycle count bound
  
  STATUS: Compilable definitions, sorry'd proofs.
  Blueprint for formalization, not a finished artifact.
-/

import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fin.Basic

open Equiv Equiv.Perm Fintype

/-! ## 1. Total Cycle Count

Mathlib's `cycleType.card` counts only nontrivial cycles (length ≥ 2).
The genus formula needs ALL cycles, including fixed points (1-cycles).
We define `numCycles` as the sum of nontrivial cycles and fixed points.

CRITICAL: Using `cycleType.card` alone gives wrong genera.
For γπ = (1,3,5)(2)(4)(6), cycleType.card = 1 but numCycles = 4.
The genus formula requires 4, not 1.
-/

/-- Total number of cycles of a permutation, including fixed points. -/
def numCycles {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) : ℕ :=
  σ.cycleType.card + card (Function.fixedPoints σ)

/-- numCycles equals card α minus the sum of (cycle_length - 1) over
    nontrivial cycles. Equivalently, it is the number of orbits of σ. -/
theorem numCycles_eq_num_orbits {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm α) :
    numCycles σ = (MulAction.orbitRel.Quotient (Subgroup.zpowers σ) α).toFinset.card := by
  sorry

/-! ## 2. The Long Cycle

The canonical cyclic permutation on Fin (2n), sending i ↦ i + 1 mod 2n.
Mathlib provides this as `finRotate`. Key properties we need:
- It is a single (2n)-cycle for n ≥ 1.
- `isCycle_finRotate` and `cycleType_finRotate` are available.
-/

/-- The long cycle γ on Fin (2n). -/
def longCycle (n : ℕ) : Perm (Fin (2 * n)) :=
  finRotate (2 * n)

/-- For n ≥ 1, the long cycle is a single cycle of length 2n. -/
theorem longCycle_isCycle {n : ℕ} (hn : 1 ≤ n) :
    (longCycle n).IsCycle := by
  unfold longCycle
  exact isCycle_finRotate (by omega : 2 ≤ 2 * n)

/-! ## 3. Pairings as a Subtype

A pairing is a fixed-point-free involution. Making it a subtype
avoids carrying proof terms through every definition and theorem.
-/

/-- A permutation is a pairing if it is an involution with no fixed points. -/
def IsPairing {n : ℕ} (π : Perm (Fin (2 * n))) : Prop :=
  π ^ 2 = 1 ∧ ∀ x, π x ≠ x

/-- The type of pairings of Fin (2n). -/
def Pairing (n : ℕ) :=
  { π : Perm (Fin (2 * n)) // IsPairing π }

instance (n : ℕ) : CoeOut (Pairing n) (Perm (Fin (2 * n))) :=
  ⟨Subtype.val⟩

/-! ## 4. Genus

Genus is defined as a plain function on pairings.
For a pairing π, the composition γπ is a permutation of Fin(2n),
and its total cycle count determines the genus via:

  genus(π) = (n + 1 - numCycles(γ * π)) / 2

We prove separately that for pairings:
(a) numCycles(γ * π) ≤ n + 1, so the numerator is nonneg
(b) the numerator is always even, so division is exact
-/

/-- The genus of a pairing. -/
def Pairing.genus {n : ℕ} (p : Pairing n) : ℕ :=
  ((n + 1) - numCycles (longCycle n * p.val)) / 2

/-- For any pairing, numCycles(γπ) ≤ n + 1. -/
theorem Pairing.numCycles_le {n : ℕ} (p : Pairing n) :
    numCycles (longCycle n * p.val) ≤ n + 1 := by
  sorry

/-- For any pairing, (n + 1 - numCycles(γπ)) is even. -/
theorem Pairing.genus_exact {n : ℕ} (p : Pairing n) :
    2 * p.genus = (n + 1) - numCycles (longCycle n * p.val) := by
  sorry

/-! ## 5. Noncrossing Predicate (Recursive)

A noncrossing pairing is defined recursively:
- The empty pairing (n = 0) is noncrossing.
- A pairing on 2n points is noncrossing if there exists an
  adjacent pair (i, i+1 mod 2n) in the pairing whose removal
  yields a noncrossing pairing on 2(n-1) points.

"Adjacent" means: π(i) = finRotate(i), i.e., π sends some
element to its cyclic successor.

This definition is better for Lean than the "no crossing arcs"
formulation because:
1. It is structurally recursive (induction is immediate).
2. It aligns with Catalan recursion.
3. It avoids the cyclic-order normalization headaches.
-/

/-- An adjacent pair in a pairing: a point i such that π(i) = i + 1 mod 2n. -/
def Pairing.hasAdjacentAt {n : ℕ} (p : Pairing n) (i : Fin (2 * n)) : Prop :=
  p.val i = finRotate (2 * n) i

/-- Deletion of an adjacent pair: given a pairing with π(i) = i+1,
    remove the pair {i, i+1} and reindex to get a pairing on 2(n-1) points.
    
    This requires careful construction. The idea:
    1. Let j = finRotate(i) = i + 1 mod 2n.
    2. Define the restriction of π to Fin(2n) \ {i, j}.
    3. Identify Fin(2n) \ {i, j} with Fin(2(n-1)) via an order-preserving map.
    4. Show the resulting permutation is again a pairing.
    
    This is the most technically demanding definition in the file.
    It requires building the injection Fin(2n-2) ↪ Fin(2n) that
    skips i and j, and proving the conjugated permutation is
    a fixed-point-free involution. -/
def Pairing.deleteAdjacent {n : ℕ} (p : Pairing (n + 1))
    (i : Fin (2 * (n + 1))) (h : p.hasAdjacentAt i) :
    Pairing n := by
  sorry -- Construction: restriction + reindexing

/-- Recursive noncrossing predicate. -/
def Pairing.IsNoncrossing : {n : ℕ} → Pairing n → Prop
  | 0, _ => True
  | n + 1, p => ∃ i : Fin (2 * (n + 1)),
      ∃ h : p.hasAdjacentAt i, (p.deleteAdjacent i h).IsNoncrossing

/-! ## 6. The Bridge Theorem (Three Stages)

Following GPT's decomposition, we prove the equivalence in stages:

Stage A: numCycles(γπ) ≤ n + 1 for all pairings (upper bound)
Stage B: numCycles(γπ) = n + 1 → noncrossing (equality → noncrossing)
Stage C: noncrossing → numCycles(γπ) = n + 1 (noncrossing → equality)

Then genus = 0 ↔ numCycles = n + 1 ↔ noncrossing.
-/

/-- Stage A: Universal upper bound on cycle count. -/
-- This is Pairing.numCycles_le above.

/-- Stage B: If the cycle count achieves its maximum, the pairing
    is noncrossing.
    
    Proof sketch (contrapositive): if π has a crossing, then the
    two crossing chords force a cycle merger in γπ, reducing the
    count below n + 1. The merger happens because a crossing
    creates a "shortcut" in the orbit of γπ that joins two
    otherwise-separate cycles. -/
theorem Pairing.maxCycles_imp_noncrossing {n : ℕ} (p : Pairing n)
    (h : numCycles (longCycle n * p.val) = n + 1) :
    p.IsNoncrossing := by
  sorry

/-- Stage C: Noncrossing pairings achieve maximum cycle count.
    
    Proof: induction on n using the recursive noncrossing definition.
    Base case (n = 0): trivial (numCycles of identity on Fin 0 = 1 = 0 + 1).
    Inductive step: if p is noncrossing, it has an adjacent pair at
    some i. Deleting this pair gives a noncrossing pairing p' on 2n
    points with numCycles(γ' * p') = n + 1 by induction. Show that
    reinserting the adjacent pair increases numCycles by exactly 1
    (the adjacent pair "splits" a cycle of γπ into two). Therefore
    numCycles(γ * p) = (n + 1) + 1 = n + 2 = (n+1) + 1.
    
    The cycle-splitting lemma is the key technical ingredient. -/
theorem Pairing.noncrossing_imp_maxCycles {n : ℕ} (p : Pairing n)
    (h : p.IsNoncrossing) :
    numCycles (longCycle n * p.val) = n + 1 := by
  sorry

/-- The cycle-splitting lemma: inserting an adjacent pair into a
    pairing increases numCycles(γπ) by 1. -/
theorem numCycles_insert_adjacent {n : ℕ} (p : Pairing n)
    (i : Fin (2 * (n + 1))) :
    -- [precise statement involving deleteAdjacent inverse]
    sorry := by
  sorry

/-! ## 7. Main Theorem and Corollary -/

/-- **The Bridge Theorem**: genus zero ↔ noncrossing. -/
theorem Pairing.genus_zero_iff_noncrossing {n : ℕ} (p : Pairing n) :
    p.genus = 0 ↔ p.IsNoncrossing := by
  constructor
  · -- genus = 0 → numCycles = n+1 → noncrossing
    intro hg
    have hc : numCycles (longCycle n * p.val) = n + 1 := by
      -- genus = 0 means (n+1 - numCycles)/2 = 0
      -- combined with numCycles ≤ n+1, this forces equality
      sorry
    exact p.maxCycles_imp_noncrossing hc
  · -- noncrossing → numCycles = n+1 → genus = 0
    intro hnc
    have hc := p.noncrossing_imp_maxCycles hnc
    -- genus = (n+1 - (n+1))/2 = 0
    sorry

/-- **Corollary**: the number of genus-zero pairings equals Cₙ. -/
theorem Pairing.genus_zero_count {n : ℕ} :
    Fintype.card { p : Pairing n // p.genus = 0 } = catalan n := by
  -- Rewrite genus = 0 as IsNoncrossing via the bridge theorem.
  -- Then count noncrossing pairings, which are Catalan.
  -- The Catalan counting for noncrossing pairings is a separate
  -- (but well-known) result that may need its own proof or
  -- connection to existing Mathlib Catalan infrastructure.
  sorry

/-! ## 8. Proof Dependencies and Estimated Effort

### Lemmas that need building (not in Mathlib):
1. `numCycles_eq_num_orbits` — total cycles = orbits of ⟨σ⟩-action
2. `Pairing.deleteAdjacent` — the deletion/reindexing construction
3. `numCycles_insert_adjacent` — the cycle-splitting lemma
4. `Pairing.numCycles_le` — upper bound on cycles for pairings
5. `Pairing.maxCycles_imp_noncrossing` — contrapositive via crossing→merger
6. `Pairing.noncrossing_imp_maxCycles` — induction via deletion

### What Mathlib provides:
- `finRotate` and `isCycle_finRotate` for the long cycle
- `Equiv.Perm.cycleType` for nontrivial cycle structure
- `Function.fixedPoints` and `Fintype.card` for fixed point count  
- `catalan` and `catalan_succ` for Catalan numbers
- Basic `Fin` arithmetic and `Perm` algebra

### Estimated scope: 800–1500 lines of Lean 4.

### The hardest part:
The deletion/reindexing machinery (Lemma 2 above). Removing two
points from Fin(2n) and reindexing to Fin(2(n-1)) while preserving
the pairing structure requires building an explicit embedding
Fin(2n-2) ↪ Fin(2n) and conjugating the permutation through it.
This is conceptually simple but technically fiddly in dependent
type theory. It is exactly the kind of thing an autoformalization
agent (Gauss, Aristotle) handles well with human scaffolding.

### The most satisfying part:
Once the bridge theorem compiles, the connection to the semicircle
law becomes a clean chain:
  E[Tr(W^{2n})/N] → trace expansion → pairing sum → genus filter
  → genus 0 = noncrossing = Catalan → semicircle moments
Each arrow is a separate formalizable step, and this file handles
the crucial middle link.
-/
