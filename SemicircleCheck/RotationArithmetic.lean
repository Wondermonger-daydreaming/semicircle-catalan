import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fin.Basic

/-!
  ROTATION ARITHMETIC: Closing the deleteAdjacent sorrys

  Refined from GPT 5.4's proof sketch. Three corrections applied:

  1. `rfl` won't fire for conjugation unfolding — need `simp [mul_apply]`
  2. `rotateToZero_apply` needs careful Fin modular arithmetic
  3. `hp_back` derivation tightened via `Equiv.apply_eq_iff_eq`

  The strategic insight (GPT's, preserved intact): isolate ALL finRotate
  arithmetic into exactly two lemmas (hρ0 and hρ1), then derive everything
  else by group theory.
-/

open Equiv Equiv.Perm

variable {n : ℕ}

/-! ## The arithmetic core

The ONLY place where finRotate arithmetic lives.
Everything else in the rotation proof is pure group theory.

Key fact: `(finRotate m) ^ k` sends `x ↦ (x + k) % m`.
This may already be in Mathlib as `finRotate_pow_apply` or similar.
If not, it needs to be proved once and never touched again.
-/

/-- Powers of finRotate act by addition mod m.
    This is the single arithmetic lemma the entire rotation
    infrastructure depends on. -/
lemma finRotate_pow_apply' {m : ℕ} (hm : 0 < m) (k : ℕ) (x : Fin m) :
    ((finRotate m) ^ k) x = ⟨(x.val + k) % m, Nat.mod_lt _ hm⟩ := by
  cases m with
  | zero => exact absurd hm (by omega)
  | succ m' =>
    induction k generalizing x with
    | zero =>
      ext; simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ, mul_apply, ih]
      congr 1
      simp only [coe_finRotate]
      split_ifs with h
      · -- x = Fin.last m': coe is 0, x.val = m'
        have hx : x.val = m' := by
          rw [Fin.ext_iff] at h; simpa [Fin.val_last] using h
        rw [hx, show m' + (k + 1) = k + (m' + 1) from by omega]
        simp [Nat.add_mod_right]
      · -- x ≠ Fin.last: coe is x.val + 1
        congr 1; omega

/-! ## The two rotation facts

Given:
  i : Fin (2 * (n + 1))
  m := 2 * (n + 1)
  ρ := (longCycle (n + 1)) ^ (m - i.val)
    = (finRotate m) ^ (m - i.val)

We need:
  hρ0 : ρ i = 0       i.e.  (i.val + (m - i.val)) % m = 0
  hρ1 : ρ (γ i) = 1   i.e.  ((i.val + 1) + (m - i.val)) % m = 1

Both reduce to trivial modular arithmetic once finRotate_pow_apply'
is available.
-/

section RotationFacts

variable (m : ℕ) (hm : 0 < m) (i : Fin m)

/-- Rotating i by (m - i.val) lands on 0.
    Morally: i + (m - i) = m ≡ 0 mod m. -/
lemma rotate_self_eq_zero :
    ((finRotate m) ^ (m - i.val)) i = ⟨0, hm⟩ := by
  rw [finRotate_pow_apply' hm]
  congr 1
  have hi : i.val < m := i.isLt
  have : i.val + (m - i.val) = m := by omega
  rw [this, Nat.mod_self]

/-- Rotating (i+1) by (m - i.val) lands on 1, provided m ≥ 2.
    Morally: (i+1) + (m - i) = m + 1 ≡ 1 mod m. -/
lemma rotate_succ_eq_one (hm2 : 2 ≤ m) :
    ((finRotate m) ^ (m - i.val)) (finRotate m i) = ⟨1, by omega⟩ := by
  rw [finRotate_pow_apply' (by omega : 0 < m)]
  congr 1
  cases m with
  | zero => omega
  | succ m' =>
    simp only [coe_finRotate]
    split_ifs with h
    · have hx : i.val = m' := by
        simp only [Fin.ext_iff, Fin.val_last] at h; exact h
      rw [hx, show 0 + (m' + 1 - m') = 1 from by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · have hi : i.val < m' := by
        simp only [Fin.ext_iff, Fin.val_last] at h
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) h
      rw [show i.val + 1 + (m' + 1 - i.val) = m' + 1 + 1 from by omega,
          Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)

end RotationFacts

/-! ## The group-theoretic layer

Once hρ0 and hρ1 are proved, everything else is algebra.
No more Fin arithmetic below this line.
-/

section GroupTheory

-- Parameterize on explicit Fin values to avoid (0 : Fin m) instance issues.
-- The group theory doesn't care what the target values are.
variable {m : ℕ} {π ρ : Perm (Fin m)}
variable {i γi a b : Fin m}

/-- If ρ sends a to b, then ρ⁻¹ sends b back to a. Pure injectivity. -/
lemma inv_apply_of_apply (h : ρ a = b) : ρ⁻¹ b = a := by
  subst h; exact ρ.symm_apply_apply a

/-- The involution gives us the reverse map.
    If π² = 1 and π(i) = γi, then π(γi) = i. -/
lemma involution_reverse (hsq : π ^ 2 = 1) (hadj : π i = γi) :
    π γi = i := by
  have h2 : π * π = 1 := by rwa [← sq]
  have h3 : π (π i) = i := by
    show (π * π) i = i; simp [h2]
  rwa [hadj] at h3

/-- Conjugation sends a to b when ρ, π, and the adjacency align.

    calc: (ρ * π * ρ⁻¹)(a) = ρ(π(ρ⁻¹(a))) = ρ(π(i)) = ρ(γi) = b -/
lemma conjugate_sends
    (hρi : ρ i = a) (hργi : ρ γi = b) (hadj : π i = γi) :
    (ρ * π * ρ⁻¹) a = b := by
  simp only [mul_apply]
  rw [inv_apply_of_apply hρi, hadj, hργi]

/-- Conjugation sends b to a (the reverse direction via involution).

    calc: (ρ * π * ρ⁻¹)(b) = ρ(π(ρ⁻¹(b))) = ρ(π(γi)) = ρ(i) = a -/
lemma conjugate_sends_back
    (hρi : ρ i = a) (hργi : ρ γi = b)
    (hsq : π ^ 2 = 1) (hadj : π i = γi) :
    (ρ * π * ρ⁻¹) b = a := by
  simp only [mul_apply]
  rw [inv_apply_of_apply hργi, involution_reverse hsq hadj, hρi]

end GroupTheory
