# x-ray-lean

Lean formalization of constructive families for binary permutation X-rays.
The main target is every admissible binary profile whose rank deviations
lie in `[-2, 2]`, at every order and without a bound on density slack.
The unrestricted conjecture remains open.

**Work in progress.** The all-order `[-2, 2]` theorem, ordinary `Q` extension
both one-sided families, and the least-counterexample restriction are proved
in Lean. The counting bounds are not yet complete. This repository is private and is not ready
for Palomar submission.

Read [PROOF.md](PROOF.md) for the informal mathematics and
[Challenge.lean](Challenge.lean) for the exact formal targets.
[VERIFICATION.md](VERIFICATION.md) records the local checks and their scope.
[DISCLOSURE.md](DISCLOSURE.md) gives the short assistance statement.

A cell in one-based row `r` and column `c` has label `r + c - 1`. An
increasing profile `L = (l₁, …, lₙ)` is admissible when its labels lie in
`[1, 2n − 1]`, every first `k` labels sum to at least `k²`, and all labels
sum to `n²`. Rank deviation is `lᵢ − (2i − 1)`.

The extension theorem takes any supplied permutation with label multiset
`L` to a permutation with labels `{3, 2n + 1} ∪ (L + 2)`. It allows repeated
labels and requires no prescribed boundary cells. The formal definitions
use `Fin n` indices, with an explicit equivalence to literal permutation
matrix labels in `XRay.realizable_iff_matrix`.

Run locally with Lean 4.33.0:

```sh
lake exe cache get
lake build XRay Challenge Solution Test
python3 scripts/check_source.py
```

There are no automatic GitHub Actions workflows. Public release and Palomar
submission are left to JD Jones after the development and verification are
complete.
