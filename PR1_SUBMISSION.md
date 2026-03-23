# PR 1 Submission Package: `finRotate` power formulas

## Zulip Post

**Topic:** `finRotate powers API for Mathlib.GroupTheory.Perm.Fin`

**Message:**

Hi, I have a small PR in mind for `Mathlib.GroupTheory.Perm.Fin`.

I'd like to add a theorem describing powers of `finRotate`:

```
((finRotate m) ^ k) x = ⟨(x.val + k) % m, ...⟩
```

for `0 < m`.

I also have a short proof that `(finRotate m) ^ m = 1`, but I'm less sure whether that should go in the same PR.

Does that sound like a reasonable addition, and is `finRotate_pow_apply` / `finRotate_pow_card` the right naming?

---

## PR Description

**Title:** `feat: add power formulas for finRotate`

**Body:**

This PR adds `finRotate_pow_apply` to `Mathlib.GroupTheory.Perm.Fin`, giving the explicit formula for the action of `(finRotate m)^k` on `Fin m`.

I also included the corollary `finRotate_pow_card`, stating `(finRotate m)^m = 1`.

This fills a small gap in the current `finRotate` API, which already contains structural results such as `support_finRotate`, `isCycle_finRotate`, and `cycleType_finRotate`.

---

## Commit Sequence

Two commits (so reviewers can accept just the first):

1. `feat: add finRotate_pow_apply`
2. `feat: add finRotate_pow_card`

Single-commit alternative: `feat: add power formulas for finRotate`

---

## Insertion Point

In `Mathlib/GroupTheory/Perm/Fin.lean`, right after `sign_finRotate` and before `support_finRotate`.

---

## Patch

See `PR1_FINROTATE_STANDALONE_PATCH.lean` for the compilable source.

The two theorems for v1 of the PR:

```lean
/-- Powers of `finRotate` act by addition modulo `m`. -/
@[simp]
theorem finRotate_pow_apply {m : ℕ} (hm : 0 < m) (k : ℕ) (x : Fin m) :
    ((finRotate m) ^ k) x = ⟨(x.val + k) % m, Nat.mod_lt _ hm⟩ := by
  cases m with
  | zero => exact absurd hm (by omega)
  | succ m' =>
    induction k generalizing x with
    | zero =>
      ext
      simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ, Perm.mul_apply, ih]
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
@[simp]
theorem finRotate_pow_card {m : ℕ} (hm : 0 < m) : (finRotate m) ^ m = 1 := by
  ext x : 1
  have h := finRotate_pow_apply hm m x
  simp only [Equiv.Perm.coe_one, id_eq] at h ⊢
  rw [h]
  exact Fin.ext (by simp [Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt])
```

---

## Reserve Corollaries (for follow-up if requested)

```lean
theorem finRotate_pow_sub_val_apply_zero {m : ℕ} (hm : 0 < m) (i : Fin m) :
    ((finRotate m) ^ (m - i.val)) i = ⟨0, hm⟩

theorem finRotate_pow_sub_val_apply_one {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    ((finRotate m) ^ (m - i.val)) (finRotate m i) = ⟨1, by omega⟩
```

---

## Pre-Push Checklist

- [ ] Post Zulip message, wait for feedback
- [ ] Fork `leanprover-community/mathlib4`
- [ ] Insert after `sign_finRotate` in `Mathlib/GroupTheory/Perm/Fin.lean`
- [ ] `lake exe cache get && lake build`
- [ ] No extra imports added
- [ ] Docstrings are one-liners matching surrounding style
- [ ] If lint complains about `@[simp]` on `finRotate_pow_card`, drop it
