# Constructive families for binary permutation X-rays

This repository proves three constructive results in Lean:

- Every admissible binary profile with rank deviations in `[-2, 2]` has a permutation realization, at every order.
- The one-sided families `dᵢ ≥ -1` and `dᵢ ≤ 1` are realizable, with at least `2ᵘ` realizations, where `u` counts positive and negative deviations respectively.
- Every supplied permutation with label multiset `L` extends to one with labels `{3, 2n + 1} ∪ (L + 2)`. For interior source labels this gives an injection between fibers.

The proofs also restrict the endpoint deviations of a least-order counterexample.
The unrestricted binary X-ray conjecture remains open.

A cell in one-based row `r` and column `c` has label `r + c - 1`. An increasing
profile `L = (l₁, …, lₙ)` is admissible when its labels lie in `[1, 2n − 1]`,
every first `k` labels sum to at least `k²`, and all labels sum to `n²`.
Its rank deviations are `dᵢ = lᵢ − (2i − 1)`.
The interval theorem bounds these deviations, with no bound on order or density slack.

[PROOF.md](PROOF.md) gives the mathematical note and references.
[Challenge.lean](Challenge.lean) states all eight principal formal claims;
[Solution.lean](Solution.lean) imports their proofs.
[VERIFICATION.md](VERIFICATION.md) records the checks and their limits.
[DISCLOSURE.md](DISCLOSURE.md) gives the short assistance statement.

The proofs use integer cells, paths of partial permutations, cycle orientation,
and induction. They do not rely on a finite census or solver output. The minimum
edge in the lower one-sided family is retained by the formal construction.
The extension allows repeated source labels and requires no prescribed boundary cells.

This is a private development prepared for JD Jones to release and submit.
No source-author endorsement or independent human review is claimed. The detailed
comparison with Brualdi–Fritscher's 2014 construction section remains outstanding;
this repository does not claim worldwide priority.

Run locally with the pinned Lean and Mathlib versions:

```sh
lake exe cache get
lake build
python3 scripts/check_source.py
python3 scripts/check_release.py
```

There are no GitHub Actions workflows. See the verification record for local
Comparator and NanoDa instructions.
