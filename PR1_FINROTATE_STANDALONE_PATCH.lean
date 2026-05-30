import Mathlib.GroupTheory.Perm.Fin

open Equiv Equiv.Perm

/-!
Draft standalone patch for Mathlib PR 1.

Proposed names for the first PR:
* `finRotate_pow_apply`                     -- local `finRotate_pow_apply'`
* `finRotate_pow_card`                      -- local `finRotate_pow_self'`

The two `m - i.val` corollaries in `SemicircleCheck.FinRotateLemmas` are useful
for this project, but should probably wait for a follow-up unless reviewers ask
for them in the same PR.
-/

/-- Powers of `finRotate` act by addition modulo `m`. -/
@[simp] theorem finRotate_pow_apply {m : ℕ} (hm : 0 < m) (k : ℕ) (x : Fin m) :
    ((finRotate m) ^ k) x = ⟨(x.val + k) % m, Nat.mod_lt _ hm⟩ := by
  cases m with
  | zero => exact absurd hm (by omega)
  | succ m' =>
    induction k generalizing x with
    | zero =>
      ext
      simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ, mul_apply, ih]
      congr 1
      simp only [coe_finRotate]
      split_ifs with h
      · have hx : x.val = m' := by
          rw [Fin.ext_iff] at h
          simpa [Fin.val_last] using h
        rw [hx, show m' + (k + 1) = k + (m' + 1) from by omega]
        simp [Nat.add_mod_right]
      · congr 1
        omega

/-- Rotating `Fin m` by `m` steps is the identity permutation. -/
theorem finRotate_pow_card {m : ℕ} (hm : 0 < m) : (finRotate m) ^ m = 1 := by
  ext x : 1
  have h := finRotate_pow_apply hm m x
  simp only [Equiv.Perm.coe_one, id_eq] at h ⊢
  rw [h]
  exact Fin.ext (by simp [Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt])
