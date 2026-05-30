# Next steps

This is the working queue after the repository inspection.

## Immediate

1. Run the build locally:

```bash
lake build
```

If the cache is missing or stale:

```bash
lake exe cache get
lake build
```

2. Verify the standalone PR 1 patch:

```bash
lake env lean PR1_FINROTATE_STANDALONE_PATCH.lean
```

3. Start the PR 1 extraction branch:

```bash
git checkout -b mathlib/finRotate-pow-apply
```

## PR 1: `finRotate` power formulas

Source:

- `SemicircleCheck/FinRotateLemmas.lean`
- `PR1_FINROTATE_STANDALONE_PATCH.lean`
- `PR1_MATHLIB_DIFF.patch`
- `PR1_SUBMISSION.md`

Remaining work:

- Check whether Mathlib already has an equivalent theorem under another name beyond the searched `finRotate_pow*` names.
- Run the standalone patch against Mathlib's import context.
- Post the prepared Zulip message from `PR1_SUBMISSION.md` and adjust names if reviewers suggest changes.
- Apply `PR1_MATHLIB_DIFF.patch` to a fresh Mathlib branch and run CI locally.

Decisions made in this package:

- Insertion point: after `sign_finRotate`, before `support_finRotate`.
- First PR scope: `finRotate_pow_apply` and `finRotate_pow_card` only.
- The two `m - i.val` corollaries are kept as reserve/follow-up material.

## PR 2: total cycle count API

Source:

- `Equiv.Perm.numCycles` in `SemicircleCheck/GenusNoncrossing.lean`
- private lemmas around lines 101-388, especially:
  - `numCycles_le_card`
  - `numCycles_conj`
  - `numCycles_eq_card_imp_one`
  - `numCycles_swap_mul_of_apply`
  - `numCycles_swap_mul_le`
  - `numCycles_mul_swap_le`

Remaining work:

- Decide whether `numCycles` should be defined by `cycleType.card + fixedPoints.card` or by orbit/cardinality infrastructure if Mathlib has a better API.
- Make the useful private lemmas public with Mathlib-style names.
- Golf the transposition-bound proof; it is the largest risk for PR 2.
- Find the right target file, likely near `Mathlib.GroupTheory.Perm.Cycle.Type`.

## PR 3: even cardinality under fixed-point-free involution

Source:

- `SemicircleCheck/EvenCard.lean`

Remaining work:

- Find the best Mathlib home.
- Check if Mathlib already has a matching finite-orbit parity theorem.
- Generalize the statement if reviewers prefer a set/subtype formulation over `Finset` closure.
- Run the file against minimal imports and remove unused imports.

## PR 4: noncrossing pairings and Catalan count

Source:

- `SemicircleCheck/ShiftTwoEquiv.lean`
- `SemicircleCheck/RotationArithmetic.lean`
- `SemicircleCheck/GenusNoncrossing.lean`
- `SemicircleCheck/CatalanRecurrence.lean`

Remaining work:

- Wait for PRs 1-3 or vendor the needed lemmas temporarily.
- Split the API into smaller files if Mathlib reviewers prefer that:
  - pairings/fixed-point-free involutions
  - noncrossing predicate and crossing bridge
  - genus/cycle-count bridge
  - Catalan decomposition/counting
- Review which private lemmas should become public API.
- Add doc comments to all public definitions and theorems.
- Golf the large crossing/rotation proofs in `CatalanRecurrence.lean`.

## Documentation cleanup

- Keep `README.md`, `ABOUT.md`, `MATHLIB_PR_PLAN.md`, and `PR1_SUBMISSION.md` synchronized as the extraction branch evolves.
- After each successful build, update the status line in `README.md` or this file with the exact command used.
