/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Berge maximum theorem (compact codomain, semicontinuity)

Small Berge-type lemmas: if a correspondence `s : X → Set Y` has a closed graph and nonempty
compact values (here obtained as closed subsets of a compact space `Y`), then the value functions

`x ↦ sSup (f x '' s x)` and `x ↦ sInf (f x '' s x)`

inherit semicontinuity properties from the integrand.

The proof uses that `Prod.fst : X × Y → X` is a closed map when `Y` is compact, so the relevant
super/sub-level sets are projections of closed subsets of `X × Y`.

## Main results

- `BergeMaximum.upperSemicontinuous_sSup_image_of_isClosed_graph`
- `BergeMaximum.lowerSemicontinuous_sInf_image_of_isClosed_graph`
-/

namespace BergeMaximum

open scoped Classical

section

section OrderLemmas

variable {X Y α : Type*}
variable [ConditionallyCompleteLinearOrder α]

variable (s : X → Set Y)
variable (f : X → Y → α)

private lemma sSup_eq_of_isMaxOn {x : X} {yMax : Y} (hyMax_mem : yMax ∈ s x)
    (hyMax_max : IsMaxOn (fun y : Y => f x y) (s x) yMax) :
    sSup (f x '' s x) = f x yMax := by
  have hyMax_ge : ∀ y ∈ s x, f x y ≤ f x yMax :=
    (isMaxOn_iff.1 hyMax_max)
  have hgreat : IsGreatest (f x '' s x) (f x yMax) := by
    refine ⟨?_, ?_⟩
    · exact ⟨yMax, hyMax_mem, rfl⟩
    · intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact hyMax_ge y hy
  simpa using hgreat.csSup_eq

private lemma sInf_eq_of_isMinOn {x : X} {yMin : Y} (hyMin_mem : yMin ∈ s x)
    (hyMin_min : IsMinOn (fun y : Y => f x y) (s x) yMin) :
    sInf (f x '' s x) = f x yMin := by
  have hyMin_le : ∀ y ∈ s x, f x yMin ≤ f x y :=
    (isMinOn_iff.1 hyMin_min)
  have hleast : IsLeast (f x '' s x) (f x yMin) := by
    refine ⟨?_, ?_⟩
    · exact ⟨yMin, hyMin_mem, rfl⟩
    · intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact hyMin_le y hy
  simpa using hleast.csInf_eq

end OrderLemmas

section

variable {X Y α : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [CompactSpace Y]
variable [ConditionallyCompleteLinearOrder α]

variable (s : X → Set Y)
variable (f : X → Y → α)

/-- The feasible-pair graph of a correspondence. -/
def graph : Set (X × Y) :=
  {p | p.2 ∈ s p.1}

private lemma isClosed_fst_image (T : Set (X × Y)) (hT : IsClosed T) :
    IsClosed (Prod.fst '' T) :=
  (isClosedMap_fst_of_compactSpace (X := X) (Y := Y)) T hT

/-- Berge-type theorem (sup version): with compact `Y`, closed graph, and nonempty closed values,
the supremum value function is upper semicontinuous provided the integrand is
upper semicontinuous. -/
theorem upperSemicontinuous_sSup_image_of_isClosed_graph
    (hs_closed : ∀ x, IsClosed (s x))
    (hs_nonempty : ∀ x, (s x).Nonempty)
    (hs_graph : IsClosed (graph (s := s)))
    (hf : UpperSemicontinuous (Function.uncurry f)) :
    UpperSemicontinuous fun x => sSup (f x '' s x) := by
  classical
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro a
  let T : Set (X × Y) := graph (s := s) ∩ (Function.uncurry f ⁻¹' Set.Ici a)
  have hT_closed : IsClosed T := by
    refine hs_graph.inter ?_
    exact (upperSemicontinuous_iff_isClosed_preimage.1 hf) a
  have hproj_closed : IsClosed (Prod.fst '' T) :=
    isClosed_fst_image (X := X) (Y := Y) (T := T) hT_closed
  have hs_compact : ∀ x, IsCompact (s x) := by
    intro x
    exact (hs_closed x).isCompact
  have hf_slice : ∀ x, UpperSemicontinuous fun y : Y => f x y := by
    intro x
    have hSlice : (Function.uncurry f ∘ fun y : Y => (x, y)) =
        (fun y : Y => f x y) := by
      funext y
      rfl
    rw [← hSlice]
    exact UpperSemicontinuous.comp hf
      (continuous_const.prodMk continuous_id)
  have hpre :
      (fun x => sSup (f x '' s x)) ⁻¹' Set.Ici a = Prod.fst '' T := by
    ext x
    constructor
    · intro hx
      rcases
          UpperSemicontinuousOn.exists_isMaxOn
            (f := fun y : Y => f x y)
            (s := s x)
            (hs_nonempty x)
            (hs_compact x)
            ((hf_slice x).upperSemicontinuousOn _)
        with ⟨yMax, hyMax_mem, hyMax_max⟩
      have hEqMax :
          sSup (f x '' s x) = f x yMax :=
        sSup_eq_of_isMaxOn (s := s) (f := f) (x := x) (yMax := yMax) hyMax_mem hyMax_max
      have ha_le : a ≤ f x yMax := by
        simpa [hEqMax] using hx
      refine ⟨(x, yMax), ?_, rfl⟩
      refine ⟨hyMax_mem, ?_⟩
      simpa [T, Function.uncurry, Set.mem_Ici] using ha_le
    · rintro ⟨p, hpT, rfl⟩
      have hp_graph : p.2 ∈ s p.1 := hpT.1
      have ha_le_f : a ≤ f p.1 p.2 := by
        simpa [T, Function.uncurry, Set.mem_Ici] using hpT.2
      rcases
          UpperSemicontinuousOn.exists_isMaxOn
            (f := fun y : Y => f p.1 y)
            (s := s p.1)
            (hs_nonempty p.1)
            (hs_compact p.1)
            ((hf_slice p.1).upperSemicontinuousOn _)
        with ⟨yMax, hyMax_mem, hyMax_max⟩
      have hyMax_ge : ∀ y ∈ s p.1, f p.1 y ≤ f p.1 yMax :=
        (isMaxOn_iff.1 hyMax_max)
      have hEqMax :
          sSup (f p.1 '' s p.1) = f p.1 yMax :=
        sSup_eq_of_isMaxOn (s := s) (f := f) (x := p.1) (yMax := yMax) hyMax_mem hyMax_max
      have ha_le_yMax : a ≤ f p.1 yMax :=
        le_trans ha_le_f (hyMax_ge p.2 hp_graph)
      have : a ≤ sSup (f p.1 '' s p.1) := by
        simpa [hEqMax] using ha_le_yMax
      exact this
  simpa [hpre] using hproj_closed

/-- Berge-type theorem (inf version): with compact `Y`, closed graph, and nonempty closed values,
the infimum value function is lower semicontinuous provided the integrand is
lower semicontinuous. -/
theorem lowerSemicontinuous_sInf_image_of_isClosed_graph
    (hs_closed : ∀ x, IsClosed (s x))
    (hs_nonempty : ∀ x, (s x).Nonempty)
    (hs_graph : IsClosed (graph (s := s)))
    (hf : LowerSemicontinuous (Function.uncurry f)) :
    LowerSemicontinuous fun x => sInf (f x '' s x) := by
  classical
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  let T : Set (X × Y) := graph (s := s) ∩ (Function.uncurry f ⁻¹' Set.Iic a)
  have hT_closed : IsClosed T := by
    refine hs_graph.inter ?_
    exact (lowerSemicontinuous_iff_isClosed_preimage.1 hf) a
  have hproj_closed : IsClosed (Prod.fst '' T) :=
    isClosed_fst_image (X := X) (Y := Y) (T := T) hT_closed
  have hs_compact : ∀ x, IsCompact (s x) := by
    intro x
    exact (hs_closed x).isCompact
  have hf_slice : ∀ x, LowerSemicontinuous fun y : Y => f x y := by
    intro x
    have hSlice : (Function.uncurry f ∘ fun y : Y => (x, y)) =
        (fun y : Y => f x y) := by
      funext y
      rfl
    rw [← hSlice]
    exact LowerSemicontinuous.comp hf
      (continuous_const.prodMk continuous_id)
  have hpre :
      (fun x => sInf (f x '' s x)) ⁻¹' Set.Iic a = Prod.fst '' T := by
    ext x
    constructor
    · intro hx
      rcases
          LowerSemicontinuousOn.exists_isMinOn
            (f := fun y : Y => f x y)
            (s := s x)
            (hs_nonempty x)
            (hs_compact x)
            ((hf_slice x).lowerSemicontinuousOn _)
        with ⟨yMin, hyMin_mem, hyMin_min⟩
      have hEqMin :
          sInf (f x '' s x) = f x yMin :=
        sInf_eq_of_isMinOn (s := s) (f := f) (x := x) (yMin := yMin) hyMin_mem hyMin_min
      have ha_ge : f x yMin ≤ a := by
        simpa [hEqMin] using hx
      refine ⟨(x, yMin), ?_, rfl⟩
      refine ⟨hyMin_mem, ?_⟩
      simpa [T, Function.uncurry, Set.mem_Iic] using ha_ge
    · rintro ⟨p, hpT, rfl⟩
      have hp_graph : p.2 ∈ s p.1 := hpT.1
      have ha_ge_f : f p.1 p.2 ≤ a := by
        simpa [T, Function.uncurry, Set.mem_Iic] using hpT.2
      rcases
          LowerSemicontinuousOn.exists_isMinOn
            (f := fun y : Y => f p.1 y)
            (s := s p.1)
            (hs_nonempty p.1)
            (hs_compact p.1)
            ((hf_slice p.1).lowerSemicontinuousOn _)
        with ⟨yMin, hyMin_mem, hyMin_min⟩
      have hyMin_le : ∀ y ∈ s p.1, f p.1 yMin ≤ f p.1 y :=
        (isMinOn_iff.1 hyMin_min)
      have hEqMin :
          sInf (f p.1 '' s p.1) = f p.1 yMin :=
        sInf_eq_of_isMinOn (s := s) (f := f) (x := p.1) (yMin := yMin) hyMin_mem hyMin_min
      have ha_ge_yMin : f p.1 yMin ≤ a :=
        le_trans (hyMin_le p.2 hp_graph) ha_ge_f
      have : sInf (f p.1 '' s p.1) ≤ a := by
        simpa [hEqMin] using ha_ge_yMin
      exact this
  simpa [hpre] using hproj_closed

end

end

end BergeMaximum
