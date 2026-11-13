# berge-maximum

[![Lean verification](https://github.com/abenenson/berge-maximum/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/abenenson/berge-maximum/actions/workflows/lean.yml)

Berge's maximum theorem for correspondences in a compact ambient decision space,
formalized in Lean with Mathlib.

For a correspondence `s : X → Set Y` and objective `f : X → Y → α`, assume:

- `Y` is a compact topological space;
- `s` has closed graph, nonempty values, and is lower hemicontinuous;
- `f` is jointly continuous;
- `α` is a conditionally complete linear order with its order topology.

Then `x ↦ sSup (f x '' s x)` is continuous. The feasible maximizers form a
nonempty, compact-valued, upper hemicontinuous correspondence. The minimum-value
result follows by order duality. No compactness or separation assumption on `X`
is needed. Closed fibers follow from closed graph and are not a separate hypothesis.

## API

```lean
import BergeMaximum
-- Opt-in checked examples:
import BergeMaximumExamples
```

The main declarations in namespace `BergeMaximum` are:

- `continuous_sSup_image_of_isClosed_graph` and
  `continuous_sInf_image_of_isClosed_graph`: continuous maximum and minimum values.
- `argmax_nonempty`, `isCompact_argmax`, and `upperHemicontinuous_argmax`:
  existence, compactness, and upper hemicontinuity of feasible maximizers.
- `upperSemicontinuous_sSup_image_of_isClosed_graph` and its infimum dual:
  one-sided results for semicontinuous objectives, requiring only nonempty values
  and closed graph in the compact ambient space.

`graph s = {p | p.2 ∈ s p.1}` and
`argmax s f x = {y | y ∈ s x ∧ f x y = sSup (f x '' s x)}`.
The standalone lower-semicontinuity lemma also works with compact fibers in an
arbitrary ambient decision space.

## Examples and limits

[BergeMaximumExamples.Basic](BergeMaximumExamples/Basic.lean) checks quadratic
optimization on `[0,1]`. Its varying correspondence has feasible sets `{0,x}` and
payoff `-(y - (2*x - 1))²`. The maximum value is continuous, its argmax sets are
nonempty and compact, and the argmax correspondence is upper hemicontinuous.
A checked calculation shows that zero maximizes at `x = 1/2` and does not maximize
at `x = 1`. The feasible sets at zero and one differ.

This package proves the classical theorem within a **compact ambient** decision
space. It does not cover all compact-valued correspondences in noncompact spaces
or prove existence of continuous optimizer selections. Closed graph alone gives
the one-sided value theorem; the full value theorem additionally uses lower
hemicontinuity. These are formalizations of classical results, with no novelty claim.
Mathlib's existing fixed-compact-set continuity and hemicontinuity APIs are discussed
in the [source comparison](docs/overlap-audit.md).

The classical reference is Claude Berge, *Topological Spaces*, Oliver and Boyd, 1963.

## Build

Supported versions: Lean **4.35.0**, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. All dependencies are locked in
`lake-manifest.json`.

```bash
python3 scripts/fetch_mathlib_cache.py
lake --rehash --wfail build
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

The verifier checks every authored module and example with all 16 linters and
warnings fatal, and audits every named public declaration's transitive axioms.
Only `Classical.choice`, `Quot.sound`, and `propext` are allowed.
It removes authored Lean build artifacts before the exact build and retains dependency caches.
See [verification and historical qualification notes](docs/overview.md) for details.
Local verification does not establish a hosted CI result or public release.

Copyright 2026 Adam Benenson; Apache 2.0. [LICENSE](LICENSE), [NOTICE](NOTICE), and
[ORIGIN.json](ORIGIN.json) record licensing and the initial public file inventory.
The inventory hashes identify the initial public adaptation; the present proofs
and added maximum-theorem module include subsequent development.

The fresh [compatibility qualification](docs/compatibility-qualification.json) records this pair.
