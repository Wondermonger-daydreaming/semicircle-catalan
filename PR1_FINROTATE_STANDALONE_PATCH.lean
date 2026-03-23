import Mathlib.GroupTheory.Perm.Fin

open Equiv Equiv.Perm

/-!
Draft standalone patch for Mathlib PR 1.

Proposed names:
* `finRotate_pow_apply`                     -- local `finRotate_pow_apply'`
* `finRotate_pow_card`                      -- local `finRotate_pow_self'`
* `finRotate_pow_sub_val_apply`             -- local `rotate_self_eq_zero`
* `finRotate_pow_sub_val_apply_finRotate`   -- local `rotate_succ_eq_one`
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

/-- Rotating `i` by `m - i.val` steps lands at `0`. -/
theorem finRotate_pow_sub_val_apply {m : ℕ} (hm : 0 < m) (i : Fin m) :
    ((finRotate m) ^ (m - i.val)) i = ⟨0, hm⟩ := by
  rw [finRotate_pow_apply hm]
  congr 1
  have : i.val + (m - i.val) = m := by omega
  rw [this, Nat.mod_self]

/-- Rotating `finRotate m i` by `m - i.val` steps lands at `1`, when `m ≥ 2`. -/
theorem finRotate_pow_sub_val_apply_finRotate {m : ℕ} (hm2 : 2 ≤ m) (i : Fin m) :
    ((finRotate m) ^ (m - i.val)) (finRotate m i) = ⟨1, by omega⟩ := by
  rw [finRotate_pow_apply (by omega : 0 < m)]
  congr 1
  cases m with
  | zero => omega
  | succ m' =>
    simp only [coe_finRotate]
    split_ifs with h
    · have hx : i.val = m' := by
        simp only [Fin.ext_iff, Fin.val_last] at h
        exact h
      rw [hx, show 0 + (m' + 1 - m') = 1 from by omega]
      exact Nat.mod_eq_of_lt (by omega)
    · have hi : i.val < m' := by
        simp only [Fin.ext_iff, Fin.val_last] at h
        exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) h
      rw [show i.val + 1 + (m' + 1 - i.val) = m' + 1 + 1 from by omega,
          Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
