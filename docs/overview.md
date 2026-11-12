# Compact-ambient Berge maximum theorem

The public package now proves continuous maximum/minimum values and nonempty compact,
upper hemicontinuous argmax correspondences, under the hypotheses stated in the
[README](../README.md). The full theorem adds lower hemicontinuity and joint continuity to
the closed-graph, nonempty-value, compact-ambient hypotheses of the one-sided result.
Closed fibers are derived from closed graph. The one-sided theorem retains its broader
conditionally complete linear-order value type, without a topological-space hypothesis on
that value type. The full theorem uses the order topology.

## Organization

- `Semicontinuity`: the correspondence graph and dual value-semicontinuity theorems.
- `Maximum`: continuous values, closed fibers, and nonempty compact upper hemicontinuous argmax.

The top-level import exports the mathematical modules. `BergeMaximumExamples` is a separate
library target: it is built by the default build but is not imported by the public
root. Every source has a module description and documented public declarations.
The only external package requirement is pinned Mathlib and its public dependencies.

## Qualification contract

A fresh authored-artifact build must pass with warnings fatal. The verifier first removes
only the listed authored modules' Lean artifacts and trace/hash variants. It refuses linked
artifact directories and preserves dependency caches and unrelated outputs. Full lint recompiles
the original source contents under the same module identity, rather than linting
only an import of cached declarations. All explicit public declaration names are
listed in `verification.json`, checked against the source and audited transitively.
Private/generated declarations are not individually listed; the public audit follows
their transitive use. The lexical custom-axiom and proof-hole screen is an additional
source check, not a substitute for the transitive audit.

The CI workflow runs the same verification program with immutable action references
and read-only repository permissions. It contains no release, Pages deployment,
automatic dependency update or publishing step. A workflow definition is not a hosted
execution receipt.

## Packaging benchmark

The comparison used actual checked-out versions of the author's five public libraries:

- `cencov-petz` at `f6cf035a4c2882ae1fbc0a83416ab8142aceb676` (leanprover/lean4:v4.29.1).
- `channel-capacity` at `fdb4d1d18dba3e408fbe1969e09a4da3da2e313e` (leanprover/lean4:v4.29.1).
- `compact-spectral` at `72cd62dbdd4c397d26fc0c5777d60fea2211e938` (leanprover/lean4:v4.29.1).
- `godel-loeb` at `60a7a1098c34dbd0ee0833dde94ef5315f22d472` (leanprover/lean4:v4.29.1).
- `rellich-kondrachov` at `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23` (leanprover/lean4:v4.29.1).

The baseline practices retained here are a small public root, Mathlib-only dependencies,
explicit mathematical scope, per-file authorship/license notices and usage documentation.
The additional gates are built examples, immutable Mathlib/action revisions, explicit
warning-fatal source/full-lint execution and a complete named public axiom ledger.
This compares observable packaging and verification practice; it does not assert that
one library's mathematics is superior to another's or that the older projects failed.

## Refreshed comparison, 2026-10-22

All five precedent remote heads were rechecked and equal the commits listed above. This is an
audit of actual source/configuration, not an inference that every earlier project ran every
present check. All five lock nine public dependencies and pin Lean4.29.1. Cencov-Petz,
compact-spectral and Rellich-Kondrachov use Lean lakefiles and retain root LICENSE files;
channel-capacity and godel-loeb use TOML lakefiles and retain root `LICENSE-APACHE` and
`LICENSE-MIT` texts; their READMEs specify dual MIT OR Apache 2.0 licensing. Authored file
notices and repository license declarations must be read together.
Channel-capacity has concrete positive/counterexample modules; the other projects have their own
scoped APIs, source checks and documentation rather than the same example layout.

This package keeps a small public root, opt-in example imports, Mathlib-only dependencies,
per-file Apache notices and an initial public file inventory. Its additional implemented gates are exact-source
builds, all16 source linters, the explicit transitive axiom ledger, durable verifier rejection
controls and always-retained CI evidence configuration. No precedent was modified or requalified.
The supported pair remains Lean4.34.1/d13f23b; earlier-pair compatibility is not inferred.

## Public file inventory and qualification

`ORIGIN.json` records the initial public path and SHA-256 digest of
`BergeMaximum/Semicontinuity.lean`. Subsequent proof refactoring is recorded in Git history.
`BergeMaximum/Maximum.lean` and expanded examples are subsequent development under the same
per-file authorship and Apache 2.0 notices.

`qualification.json` and `qualification-logs/` contain the historical October 17 run.
`private-release-qualification.json`, when present, describes the later private qualification
at its stated source identity. Neither historical receipt qualifies subsequent edits.
The current verifier writes a fresh evidence directory per invocation and retains failures.

The verifier rejects native panics, malformed/error JSON even on exit zero, unsupported import
headers, optimized Python that disables assertions, proof holes, and custom axioms. Its twelve
regression controls run with:

```bash
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The full current check remains `python3 scripts/verify.py`. CI configuration retains evidence
using a pinned upload action; a configured workflow is not a hosted execution result.
Repository visibility and release records establish publication status; local qualification
does not establish a hosted run or upstream acceptance.

## Mathematical readiness qualification

The [October 23 source qualification](readiness-qualification.json) records the compact-ambient
continuous maximum and argmax theorems, varying examples and its source hashes. Earlier
receipts remain historical. Hosted CI and final-candidate review are separate results.

The [November 4 release qualification](release-qualification.json) records a fresh warning-fatal
build of all five authored modules, all 16 linters per source, and the complete 29-name transitive
axiom audit. It binds the Lean sources, verifier, manifest, toolchain and package pins by SHA-256.
Its [retained logs](release-logs/) include the exact build, source lint, axiom audit, twelve isolated
Python controls, and resource receipts. The build log explicitly records all five modules rebuilt;
the cleanup list is empty because an earlier synthetic regression had already removed the outputs.
That regression now uses a temporary repository fixture. Historical qualification records remain
unchanged. The source/configuration inputs remained unchanged when the final Python controls ran.
Independent source review found no blocking issue in the theorem scope, examples, provenance,
verifier changes or the retained source/build/lint/axiom evidence.
