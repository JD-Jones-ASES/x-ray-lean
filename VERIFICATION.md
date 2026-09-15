# Verification

All eight statements in Challenge.lean have proofs. The complete local build,
source guard, all-declaration axiom audit, Comparator comparison, Lean kernel
replay and independent NanoDa replay pass. No GitHub Actions minutes were used.

The unrestricted binary X-ray conjecture remains open. The explicit example
words in PROOF.md are informal consequences of the general theorems. Neither
those examples nor the earlier Python census is a premise of a Lean proof.

## Formal scope

| Statement | Proof module |
| --- | --- |
| Every admissible profile with deviations in [-2, 2] is realizable | XRay/TwoSided.lean |
| Lower and upper one-sided families are realizable | XRay/OneSided.lean |
| At least 2^u realizations in the lower family | XRay/OneSidedCount.lean |
| Reflected counting bound for the upper family | XRay/ReflectionCount.lean |
| For n >= 1, realizable L implies realizable Q(L), allowing repeated labels | XRay/Extension.lean |
| For n >= 1, h(L) <= h(Q(L)) when every source label lies in [2, 2n-2] | XRay/ExtensionCount.lean |
| Endpoint restriction on a least-order counterexample | XRay/TwoSided.lean |

Here h counts permutation realizations. The two selected extension statements
assert existence and a conditional cardinality inequality, without specifying
a pointwise extension of a prescribed permutation. The injective constructions
below are supporting proof mechanisms.

The lower one-sided induction retains the minimum undirected edge.
`XRay.realizable_iff_matrix` establishes equivalence between ranked-cell
assignments and the literal label multiset of a permutation matrix.
`XRay.rooted_switch_injective` and `XRay.promotion_bits_injective` provide
inverses for the counting constructions. No finite cap occurs in the theorems.

All ten mathematical definitions are explicit in Challenge.lean.
`definition_names` is empty: these are fixed definitions, not holes to be filled.
Comparator checks all eight named theorems against that fixed statement environment.
Challenge intentionally contains eight proof placeholders. Solution and its
imports contain none, and Solution does not import Challenge.

## Local checks

After correcting the extension narrative and theorem docstrings, the full build,
axiom audit, source guard, release checks, Comparator and both kernel replays
were rerun successfully. Metadata and local documentation links also pass.
Definitions, theorem types, proof terms and Comparator selection are unchanged
from commit `b8b0b87997f5dc53db961ecd33006fe324550c58`. The negative controls
below retain their earlier successful results and were not rerun for this
documentation-only correction. File hashes and check scope are recorded in
[verification/local-checks.json](verification/local-checks.json).

```sh
lake exe cache get
lake build
python3 scripts/check_source.py
python3 scripts/check_release.py
python3 scripts/check_mutations.py
```

The full build audits 724 project declarations, including private declarations,
with only `propext`, `Classical.choice` and `Quot.sound` permitted. All eight
principal declarations must be present. The source guard checks 42 solution
and audit files, rejecting placeholders, added axioms and kernel bypasses.

Test/Controls.lean checks loops, parallel edges, a degree violation, repeated
matrix labels and reflection. The mutation checks deliberately insert a proof
placeholder, a native-decide bypass, and an unused false axiom. Each must be
rejected, and the original files are restored in a `finally` block.

The separate Comparator control changes the Challenge's admissibility definition
to `True` while retaining the same theorem names. Comparator must reject the
changed definition. The script restores and rebuilds the original Challenge.
Run it with the same tool environment as the ordinary comparison:

```sh
python3 scripts/check_comparator_mutation.py /path/to/comparator
```

## Comparator and independent replay

The local check uses the registry's pinned tool sources:

| Tool | Revision |
| --- | --- |
| Lean for this project and exporter | leanprover/lean4:v4.33.0 |
| Mathlib | db584cd6d46c92f209a44c0f1c829460d327499d |
| Comparator | 575674928e239f5bc452aab72d1dd7b0f1326494 |
| lean4export for Lean 4.33.0 | 15f6055e299ad5b89345e533cc2192f4cc00f659 |
| NanoDa | 68d5ca9db226849b41a6fff59d796ff19d0a8840 |

Comparator itself is built with its pinned Lean 4.34.0-rc1 toolchain. The
exporter is built with the project's Lean 4.33.0 toolchain. Dependencies are
pinned by the committed manifests; no `lake update` is needed.

After building those tools, run from the project root:

```sh
COMPARATOR_LANDRUN=/path/to/landrun \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
COMPARATOR_NANODA=/path/to/nanoda_bin \
lake env /path/to/comparator comparator.json
```

The successful run reports:

```text
nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

This desktop is macOS. The local run uses Comparator's documented
`scripts/fake-landrun.sh` development wrapper because Landrun is a Linux
sandbox. The wrapper provides no process isolation. The comparison and two
kernel checks pass; the local run does not reproduce Palomar's protected Linux
sandbox. Palomar separately checks the submitted commit in its verification
and review pipeline.

The metadata passes PalomarSubmission's `load_formalization_metadata` contract.
The repository contains the substantive proof, an MIT license, its full dependency
manifest and a Mathlib-only Challenge. No independent human review or source-author
endorsement is claimed. The unresolved Brualdi–Fritscher comparison concerns
provenance and novelty, not whether these Lean statements were checked.

## Provenance and exposition

The formal promotion inverse records the orientation bit by transposing the
whole output, and undoes that transposition before recovering the source.
The exposition may instead keep unrelated cycles fixed and reverse only the
new distinguished cycle. Both constructions have the same labels and the
same two-copy injection; this is an implementation choice, not a change to
any compared theorem.
