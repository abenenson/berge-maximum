# Mathlib overlap and theorem boundary

Source comparison refreshed 2026-10-23 against the **actual pinned dependency**:
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.

## Existing results used

- `Mathlib.Topology.Order.Compact` already proves `IsCompact.continuous_sSup` and
  `IsCompact.continuous_sInf` for a **fixed** compact feasible set and jointly continuous
  objective. This package does not present that special case as missing from Mathlib.
- `Mathlib.Topology.Semicontinuity.Basic` supplies attainment of extrema for semicontinuous
  objectives on nonempty compact sets, and the open/closed level-set characterizations.
- `Mathlib.Topology.Semicontinuity.Hemicontinuity` supplies the standard `LowerHemicontinuous`
  and `UpperHemicontinuous` predicates, their open-inverse characterizations, and
  `LowerHemicontinuous.inter_hasOpenCGraph`.
- `isClosedMap_fst_of_compactSpace` supplies the closed projection used in the upper value
  bound and in upper hemicontinuity of closed-graph correspondences.

## Package contribution

`BergeMaximum.Maximum` combines those APIs for **varying** feasible correspondences:
closed graph, nonempty values, compact ambient decision space, lower hemicontinuity, and
joint continuity yield continuous maximum values and nonempty compact upper hemicontinuous
argmax correspondences. The infimum result is derived by order duality. Lower
hemicontinuity of the value follows by intersecting feasibility with the open strict
superlevel graph and applying Mathlib's lower hemicontinuity theorem. Upper hemicontinuity
of argmax follows from its closed graph and compact ambient space. Closed fibers are
derived rather than assumed separately. The examples include genuinely varying feasible
sets and a change in the maximizing branch.

These are classical mathematical results. The contribution is this scoped formal API and
its integration with pinned Mathlib, not a claim of new mathematics. A bounded filename and
source search of the pinned topology modules found no dedicated Berge theorem for varying
correspondences; it does not prove that no equivalent formulation exists anywhere in Mathlib.
The package does not cover the full noncompact-ambient compact-valued theorem, nor assert
continuous optimizer selections or upstream acceptance.

## Historical comparison

The earlier 2026-10-22 inspection also read newer Mathlib sources at
`6ea173996caaa665b0a3c4f81ce472e04e4f7754`. That was source inspection only, not a native
compatibility result. Its semicontinuity-only package description is superseded by the
maximum-theorem module. Native support remains limited to the pinned pair above.
