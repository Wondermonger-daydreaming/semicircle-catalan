/-
  THE BRIDGE THEOREM: genus zero ↔ noncrossing
  
  This file sketches the formalization of the equivalence between
  genus-zero pairings and noncrossing pairings of {1, ..., 2n}.
  
  This is the combinatorial heart of the Wigner semicircle law:
  the fact that the 2n-th moment of the semicircle distribution
  equals the Catalan number Cₙ reduces to the fact that exactly
  the noncrossing pairings have genus zero.
  
  STATUS: Sketch / blueprint. Not yet compilable Lean 4.
  The goal is to identify exactly what definitions and lemmas
  are needed, and which parts Mathlib already provides.
-/

import Mathlib.Combinatorics.Catalan
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fin.Basic

open Equiv.Perm

/-! ## 1. Core Definitions -/

/-- A perfect matching (pairing) of Fin (2 * n) is a fixed-point-free
    involution: a permutation π with π ∘ π = id and π x ≠ x for all x. -/
def IsPairing {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) : Prop :=
  π * π = 1 ∧ ∀ x, π x ≠ x

/-- The long cycle γ = (0, 1, 2, ..., 2n-1) on Fin (2n).
    This is the cyclic permutation that shifts each element by 1. -/
def longCycle (n : ℕ) : Equiv.Perm (Fin (2 * n)) :=
  Equiv.Perm.cycleOf (Fin.mk 0 (by omega)) -- needs careful construction
  -- More precisely: γ(i) = (i + 1) mod 2n
  -- In Lean 4 with Fin arithmetic: fun i => i + 1

/-- The genus of a pairing π with respect to the long cycle γ.
    genus(π) = (n + 1 - #cycles(γ ∘ π)) / 2
    
    Note: for a pairing, n + 1 - #cycles(γπ) is always even and nonneg,
    so the division by 2 is exact and the result is a natural number. -/
def pairingGenus {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) 
    (hπ : IsPairing π) : ℕ :=
  (n + 1 - (longCycle n * π).cycleType.card) / 2
  -- Here cycleType gives the multiset of cycle lengths,
  -- and .card gives the number of cycles.
  -- Mathlib provides: Equiv.Perm.cycleType and related API.

/-- A pairing is noncrossing if no two pairs "interleave" on the circle.
    Formally: for pairs (a, π(a)) and (b, π(b)), we never have
    a < b < π(a) < π(b) or b < a < π(b) < π(a) in the cyclic order.
    
    There are several equivalent formulations. The cleanest for
    formalization might be the recursive/inductive one:
    a noncrossing pairing either is empty, or has an "adjacent" pair
    (i, i+1) whose removal yields a smaller noncrossing pairing. -/

/-- Cyclic interleaving: two arcs (a, b) and (c, d) on a circle cross
    if exactly one of c, d lies strictly between a and b. -/
def arcsCross {m : ℕ} (a b c d : Fin m) : Prop :=
  -- Using the linear order on Fin as a proxy for cyclic order
  -- (valid when a < b and c < d, which we can normalize to)
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

/-- A pairing π is noncrossing if no two of its pairs cross. -/
def IsNoncrossing {n : ℕ} (π : Equiv.Perm (Fin (2 * n))) 
    (hπ : IsPairing π) : Prop :=
  ∀ a b : Fin (2 * n), a ≠ b → π a ≠ b → π a ≠ π b → 
    ¬ arcsCross a (π a) b (π b)

/-! ## 2. The Bridge Theorem -/

/-- **Main theorem**: A pairing has genus zero if and only if
    it is noncrossing. -/
theorem genus_zero_iff_noncrossing {n : ℕ} 
    (π : Equiv.Perm (Fin (2 * n))) (hπ : IsPairing π) :
    pairingGenus π hπ = 0 ↔ IsNoncrossing π hπ := by
  sorry -- The proof
  
/-! ## 3. Corollary: the Catalan connection -/

/-- The number of genus-zero pairings of 2n points equals Cₙ. -/
theorem genus_zero_count_eq_catalan (n : ℕ) :
    Finset.card { π : Equiv.Perm (Fin (2 * n)) | 
      IsPairing π ∧ pairingGenus π (sorry) = 0 } = catalan n := by
  -- Follows from genus_zero_iff_noncrossing plus the known
  -- fact that noncrossing pairings are counted by Catalan numbers.
  sorry

/-! ## 4. Proof Strategy Notes

The proof of genus_zero_iff_noncrossing has two directions:

### (→) Noncrossing implies genus zero
  
  Induction on n. A noncrossing pairing on 2n points must contain
  at least one "adjacent" pair (i, i+1 mod 2n). Removing this pair
  gives a noncrossing pairing on 2(n-1) points. Show that removing
  an adjacent pair increases the cycle count of γπ by exactly 1
  (it "splits" a cycle). By induction, the smaller pairing has
  n cycles in γ'π', so the original has n+1 cycles, giving genus 0.

### (←) Genus zero implies noncrossing
  
  Contrapositive: if π has a crossing, show that #cycles(γπ) < n+1,
  hence genus > 0. A crossing pair (a, π(a)), (b, π(b)) forces
  a "merger" of cycles in γπ. Specifically, the crossing constraint
  means that the orbits of a and b under γπ must coincide, reducing
  the total cycle count.

### What Mathlib provides (as of early 2026):
  
  - `Equiv.Perm.cycleType` : the cycle type as a multiset of ℕ
  - `Equiv.Perm.IsCycle` : predicate for being a single cycle  
  - `Catalan` : the Catalan numbers (in `Mathlib.Combinatorics.Catalan`)
  - `Equiv.Perm.support` : the support of a permutation
  - Basic Fin arithmetic
  
### What would need to be built:
  
  - The definition of `IsPairing` (fixed-point-free involution)
  - The specific long cycle on Fin(2n) with its properties
  - The genus function for pairings
  - The noncrossing predicate (either via arc-crossing or inductively)
  - The "adjacent pair" lemma for noncrossing pairings
  - The cycle-splitting lemma for removing adjacent pairs
  - The cycle-merging lemma for crossings
  
  Estimated scope: 500-1500 lines of Lean 4, depending on how much
  supporting infrastructure for Fin-indexed permutations is needed.
-/

/-! ## 5. Connection to the Semicircle Law

Once this theorem is in place, the moment formula becomes:

  (1/N) * E[Tr(W_N^{2n})] = Σ_{g ≥ 0} ε_g(n) * N^{-2g}

where ε_0(n) = #{genus-0 pairings} = #{noncrossing pairings} = Cₙ.

The full semicircle law then follows from:
  1. The trace expansion (combinatorial identity)
  2. The genus classification (this theorem)  
  3. The Catalan counting (known in Mathlib)
  4. The moment characterization of the semicircle distribution

Steps 1 and 4 require analysis (measure theory, convergence);
steps 2 and 3 are purely combinatorial and formalizable now.
-/
