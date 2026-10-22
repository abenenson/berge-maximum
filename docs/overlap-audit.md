# Dependency overlap and private inspection scope

Source audit date: 2026-10-22. The packaged result is classical compact-ambient-codomain Berge-type
semicontinuity. It is not a claim of new mathematics or an unrestricted maximum theorem.

Current Mathlib at `6ea173996caaa665b0a3c4f81ce472e04e4f7754` has extensive
[semicontinuity](https://github.com/leanprover-community/mathlib4/blob/6ea173996caaa665b0a3c4f81ce472e04e4f7754/Mathlib/Topology/Semicontinuity/Basic.lean)
and [hemicontinuity](https://github.com/leanprover-community/mathlib4/blob/6ea173996caaa665b0a3c4f81ce472e04e4f7754/Mathlib/Topology/Semicontinuity/Hemicontinuity.lean)
APIs, including `isClosedMap_iff_upperHemicontinuous` and neighborhood characterizations of
correspondences. The present proof uses compactness and closed projections to establish its
specific supremum/infimum value semicontinuity statements. Its explicit nonempty closed values,
closed graph, compact ambient decision space and order/topological hypotheses remain in force.

A current Mathlib filename search found no dedicated Berge-named module, and the selected
semicontinuity/hemicontinuity sources did not expose this exact named theorem. That bounded
search does not establish absence of an equivalent theorem elsewhere. A future upstream
proposal would need a full API comparison and discussion of a formulation through existing
hemicontinuity/proper-map APIs; neither readiness nor acceptance is claimed.

The newer Mathlib sources were inspected, not compiled with this package. Native compatibility
is qualified only on its locked d13f23b/Lean4.34.1 pair. No external submission or public release
is included in private preparation.
