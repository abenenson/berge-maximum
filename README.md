# berge-maximum

Compact-codomain Berge semicontinuity, formalized in Lean with Mathlib only.

Private preparation. Local qualification and its exact source identities are recorded
in `docs/qualification.json` when complete. Hosted CI execution is a separate result;
no hosted pass or public release is claimed.

## Mathematical scope

Berge-type semicontinuity lemmas for feasible correspondences with a closed graph
and nonempty closed values in a compact ambient decision space.

A jointly upper-semicontinuous integrand gives an upper-semicontinuous supremum
value; the lower-semicontinuous analogue gives lower-semicontinuous infimum value.
The value codomain is a conditionally complete linear order, with the additional
topological/order hypotheses shown in each theorem signature.

This is a compact-ambient-codomain result. It is not the unrestricted Berge maximum
theorem, a lower-hemicontinuity theorem, a general optimizer-selection theorem, or a
claim that closed graph alone yields continuous maximum values. The public `graph`
helper names the same feasible-pair set used by the theorems.

## Build and verification

The supported tested pair is Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Every transitive dependency is locked in
`lake-manifest.json`. The author's earlier libraries currently pin Lean 4.29.1;
compatibility with that older pair has not been tested or claimed here.

```bash
lake exe cache get
lake --rehash --wfail build
python3 scripts/verify.py
```

The verifier builds every authored module and example, re-elaborates
each source with all 16 linters including theorem documentation, rejects warnings,
checks declaration coverage, and audits transitive axioms of every explicit public
name. Only `Classical.choice`, `Quot.sound` and `propext` are allowed. It rejects
`sorry`, `admit`, explicit custom axioms and imports outside this package/Mathlib.
Logs and receipts go into a new `verification-artifacts` directory per run; failures
are retained. It uses Python's standard library and no private verification tooling.

## Usage

```lean
import BergeMaximum
-- Examples are opt-in:
import BergeMaximumExamples
```

## Modules

- `Semicontinuity`: the correspondence graph and the two value-semicontinuity theorems.

## Checked example

`BergeMaximumExamples.Basic` treats the parametric quadratic loss `(x - y)^2` over `y ∈ [0,1]`:
its minimum value is lower semicontinuous and its maximum value is upper
semicontinuous. It also checks that empty feasibility fails the explicit nonemptiness
hypothesis.

## Provenance and license

Copyright 2026 Adam Benenson. Apache 2.0, matching the explicit notices retained in
the extracted mathematical files. See [LICENSE](LICENSE), [NOTICE](NOTICE), and
[ORIGIN.json](ORIGIN.json) for file identities and the limited extraction provenance.
No surrounding repository or unrelated source is assigned a license here.

[API and verification notes](docs/overview.md) describe the package boundary and
qualification process. These are formalizations of the scoped mathematical results;
no application-specific physical or empirical implication is claimed.
