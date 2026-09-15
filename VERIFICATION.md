# Verification

The completed library uses Lean 4.33.0 and Mathlib at
`db584cd6d46c92f209a44c0f1c829460d327499d`. The manifest pins all dependencies.
Checks run locally; no GitHub Actions minutes have been used.

The formal target remains all eight statements in Challenge.lean. At this
checkpoint, ordinary extension is complete; the other seven target statements
are pending. Supporting proofs cover degree-two orientation, equivalence with
literal matrix labels, promotion, finite source-to-sink paths, exact switching
margins and reflection. The library contains no proof placeholders.

## Local commands

```sh
lake exe cache get
lake build XRay Challenge Solution Test
python3 scripts/check_source.py
python3 scripts/check_release.py
```

Challenge.lean intentionally contains eight placeholder statements. Its
warnings are expected, and it is not imported into Solution or the axiom
audit. The source guard rejects placeholders and kernel bypasses in the
solution library. Test/Axioms.lean audits every project declaration, including
private declarations, allowing only `propext`, `Classical.choice` and
`Quot.sound`. Test/Controls.lean checks loops, parallel edges, a degree
violation and repeated matrix labels.

The release check must currently fail because seven advertised declarations
have not been proved. A successful library build therefore does not mean the
full note has been formalized. Comparator and independent NanoDa replay have
not yet run. Their configuration selects the full target list, rather than
only the already proved extension theorem.

## Statement conventions

Lean uses indices in `Fin n`, starting at zero, but labels remain one-based:
cell `(i, p i)` has label `i + p i + 1`. Strict monotonicity makes the profile
binary. `XRay.realizable_iff_matrix` proves equivalence between ranked-cell
realization and the literal multiset of a permutation matrix, including
repeated labels. `extend` lists the old shifted labels before its two new
labels; multiset equality makes this ordering irrelevant.

## Packaging reference

The public rk-lean repository was inspected for its Challenge/Solution layout,
pinned dependencies, axiom auditing and local verification commands. This
project uses the same Lean/Mathlib versions, with independently written proof
code and shorter documentation. Neither repository has automatic CI workflows.

The informal proof source is Analytic-Lab commit
`391d59f60d405155b145c69c3a4639797e4c28fd`. Finite Python verification is
background evidence, not a premise of the Lean proofs.
