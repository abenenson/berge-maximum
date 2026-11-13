/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import BergeMaximum.Semicontinuity
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# Berge's maximum theorem in a compact ambient decision space

Closed graph and nonempty values give the upper bound direction. Lower hemicontinuity
supplies the other direction for continuous objectives. The maximum value is continuous,
and the argmax correspondence has nonempty compact values and is upper hemicontinuous.

The decision space is compact; no compactness or separation assumption is imposed on the
parameter space. This does not cover arbitrary compact-valued correspondences in a
noncompact ambient space.

## Main results

- `continuous_sSup_image_of_isClosed_graph`: continuous maximum values.
- `continuous_sInf_image_of_isClosed_graph`: continuous minimum values by order duality.
- `argmax_nonempty`, `isCompact_argmax`: nonempty compact sets of feasible maximizers.
- `upperHemicontinuous_argmax`: upper hemicontinuity of the optimizer correspondence.

## References

Claude Berge, *Topological Spaces*, Oliver and Boyd, 1963.
-/

@[expose] public section

namespace BergeMaximum

open Set

variable {X Y α : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A closed correspondence graph has closed fibers, without separation assumptions. -/
theorem isClosed_fiber_of_isClosed_graph (s : X → Set Y)
    (hs : IsClosed (graph s)) (x : X) : IsClosed (s x) :=
  hs.preimage (continuous_const.prodMk continuous_id)

variable [CompactSpace Y]

/-- Closed graph in a compact ambient space implies Mathlib upper hemicontinuity. -/
theorem upperHemicontinuous_of_isClosed_graph (s : X → Set Y)
    (hs : IsClosed (graph s)) : UpperHemicontinuous s := by
  rw [upperHemicontinuous_iff_isOpen_preimage_Iic]
  intro u hu
  have hclosed : IsClosed (Prod.fst '' (graph s ∩ Prod.snd ⁻¹' uᶜ)) :=
    isClosedMap_fst_of_compactSpace _ (hs.inter (hu.isClosed_compl.preimage continuous_snd))
  have heq : s ⁻¹' Iic u = (Prod.fst '' (graph s ∩ Prod.snd ⁻¹' uᶜ))ᶜ := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_image, mem_inter_iff]
    simp [graph, Set.subset_def]
  rw [heq]
  exact hclosed.isOpen_compl

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

omit [CompactSpace Y] in
/-- Lower hemicontinuity makes the maximum value lower semicontinuous for continuous objectives.
Compact nonempty fibers ensure attained suprema. -/
theorem lowerSemicontinuous_sSup_image_of_lowerHemicontinuous
    (s : X → Set Y) (f : X → Y → α)
    (hs_compact : ∀ x, IsCompact (s x)) (hs_nonempty : ∀ x, (s x).Nonempty)
    (hs_lower : LowerHemicontinuous s) (hf : Continuous (Function.uncurry f)) :
    LowerSemicontinuous fun x => sSup (f x '' s x) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  have hmeet : LowerHemicontinuous (fun x => s x ∩ {y | a < f x y}) :=
    hs_lower.inter_hasOpenCGraph (isOpen_lt continuous_const hf)
  have hopen := (lowerHemicontinuous_iff_isOpen_inter_nonempty.mp hmeet) univ isOpen_univ
  have heq : (fun x => sSup (f x '' s x)) ⁻¹' Ioi a =
      {x | ((s x ∩ {y | a < f x y}) ∩ univ).Nonempty} := by
    ext x
    have hslice : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    obtain ⟨y, hy, heq⟩ :=
      (hs_compact x).exists_sSup_image_eq (hs_nonempty x) hslice.continuousOn
    constructor
    · intro hx
      refine ⟨y, ⟨hy, ?_⟩, mem_univ _⟩
      simpa only [mem_preimage, mem_Ioi, mem_ofPred_eq, heq] using hx
    · rintro ⟨z, ⟨hz, haz⟩, _⟩
      exact haz.trans_le (le_csSup ((hs_compact x).bddAbove_image hslice.continuousOn) ⟨z, hz, rfl⟩)
  rw [heq]
  exact hopen

/-- Berge's continuous maximum value theorem for a compact ambient decision space.
The feasible correspondence has closed graph, nonempty values and is lower hemicontinuous. -/
theorem continuous_sSup_image_of_isClosed_graph
    (s : X → Set Y) (f : X → Y → α)
    (hs_nonempty : ∀ x, (s x).Nonempty) (hs_graph : IsClosed (graph s))
    (hs_lower : LowerHemicontinuous s) (hf : Continuous (Function.uncurry f)) :
    Continuous fun x => sSup (f x '' s x) :=
  continuous_iff_lower_upperSemicontinuous.mpr
    ⟨lowerSemicontinuous_sSup_image_of_lowerHemicontinuous s f
      (fun x => (isClosed_fiber_of_isClosed_graph s hs_graph x).isCompact)
      hs_nonempty hs_lower hf,
      upperSemicontinuous_sSup_image_of_isClosed_graph s f hs_nonempty hs_graph
        hf.upperSemicontinuous⟩

/-- The continuous minimum value theorem, obtained from the maximum theorem by order duality. -/
theorem continuous_sInf_image_of_isClosed_graph
    (s : X → Set Y) (f : X → Y → α)
    (hs_nonempty : ∀ x, (s x).Nonempty) (hs_graph : IsClosed (graph s))
    (hs_lower : LowerHemicontinuous s) (hf : Continuous (Function.uncurry f)) :
    Continuous fun x => sInf (f x '' s x) :=
  continuous_sSup_image_of_isClosed_graph (α := αᵒᵈ) s f hs_nonempty hs_graph hs_lower hf

/-- Feasible maximizers, expressed as attainment of the supremum value. -/
def argmax (s : X → Set Y) (f : X → Y → α) (x : X) : Set Y :=
  {y | y ∈ s x ∧ f x y = sSup (f x '' s x)}

/-- A continuous objective attains its maximum on every nonempty closed feasible fiber. -/
theorem argmax_nonempty (s : X → Set Y) (f : X → Y → α)
    (hs_nonempty : ∀ x, (s x).Nonempty) (hs_graph : IsClosed (graph s))
    (hf : Continuous (Function.uncurry f)) (x : X) : (argmax s f x).Nonempty := by
  have hslice : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, hy, heq⟩ := (isClosed_fiber_of_isClosed_graph s hs_graph x).isCompact
    |>.exists_sSup_image_eq (hs_nonempty x) hslice.continuousOn
  exact ⟨y, hy, heq.symm⟩

omit [CompactSpace Y] in
/-- Continuous maximum values give a closed graph for the feasible maximizers. -/
theorem isClosed_graph_argmax (s : X → Set Y) (f : X → Y → α)
    (hs_graph : IsClosed (graph s)) (hf : Continuous (Function.uncurry f))
    (hv : Continuous fun x => sSup (f x '' s x)) : IsClosed (graph (argmax s f)) :=
  hs_graph.inter (isClosed_eq hf (hv.comp continuous_fst))

/-- The argmax correspondence in Berge's theorem is upper hemicontinuous. -/
theorem upperHemicontinuous_argmax (s : X → Set Y) (f : X → Y → α)
    (hs_nonempty : ∀ x, (s x).Nonempty) (hs_graph : IsClosed (graph s))
    (hs_lower : LowerHemicontinuous s) (hf : Continuous (Function.uncurry f)) :
    UpperHemicontinuous (argmax s f) :=
  upperHemicontinuous_of_isClosed_graph _ (isClosed_graph_argmax s f hs_graph hf
    (continuous_sSup_image_of_isClosed_graph s f hs_nonempty hs_graph hs_lower hf))

/-- The argmax correspondence in Berge's theorem has compact values. -/
theorem isCompact_argmax (s : X → Set Y) (f : X → Y → α)
    (hs_nonempty : ∀ x, (s x).Nonempty) (hs_graph : IsClosed (graph s))
    (hs_lower : LowerHemicontinuous s) (hf : Continuous (Function.uncurry f)) (x : X) :
    IsCompact (argmax s f x) :=
  (isClosed_fiber_of_isClosed_graph _ (isClosed_graph_argmax s f hs_graph hf
    (continuous_sSup_image_of_isClosed_graph s f hs_nonempty hs_graph hs_lower hf)) x).isCompact

end BergeMaximum
