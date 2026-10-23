/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import BergeMaximum
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Parametric quadratic optimization on a compact interval

Quadratic optimization and a genuinely varying two-point feasible correspondence illustrate
the semicontinuity and full compact-ambient maximum theorems.
-/

namespace BergeMaximum.Examples

open Set

/-- The compact decision interval of the optimization problem. -/
abbrev Decision := Icc (0 : ℝ) 1

/-- Minimum quadratic loss over the unit interval varies lower semicontinuously. -/
theorem quadratic_minimum_lsc :
    LowerSemicontinuous fun parameter : ℝ ↦
      sInf ((fun decision : Decision ↦ (parameter - (decision : ℝ)) ^ 2) '' univ) := by
  apply lowerSemicontinuous_sInf_image_of_isClosed_graph
    (s := fun _ : ℝ ↦ (univ : Set Decision))
  · exact fun _ ↦ ⟨⟨0, by norm_num⟩, mem_univ _⟩
  · simpa only [graph, mem_univ, ofPred_true] using
      (isClosed_univ : IsClosed (univ : Set (ℝ × Decision)))
  · exact (by fun_prop : Continuous
      (Function.uncurry fun parameter : ℝ ↦
        fun decision : Decision ↦ (parameter - (decision : ℝ)) ^ 2)).lowerSemicontinuous

/-- Maximum quadratic loss over the same compact interval is upper semicontinuous. -/
theorem quadratic_maximum_usc :
    UpperSemicontinuous fun parameter : ℝ ↦
      sSup ((fun decision : Decision ↦ (parameter - (decision : ℝ)) ^ 2) '' univ) := by
  apply upperSemicontinuous_sSup_image_of_isClosed_graph
    (s := fun _ : ℝ ↦ (univ : Set Decision))
  · exact fun _ ↦ ⟨⟨0, by norm_num⟩, mem_univ _⟩
  · simpa only [graph, mem_univ, ofPred_true] using
      (isClosed_univ : IsClosed (univ : Set (ℝ × Decision)))
  · exact (by fun_prop : Continuous
      (Function.uncurry fun parameter : ℝ ↦
        fun decision : Decision ↦ (parameter - (decision : ℝ)) ^ 2)).upperSemicontinuous

/-- The zero decision in the unit interval. -/
def zeroDecision : Decision := ⟨0, by norm_num⟩

/-- A varying feasible set: the fixed zero decision and the current parameter. -/
def movingDecisions (parameter : Decision) : Set Decision :=
  {zeroDecision} ∪ {parameter}

/-- Every moving feasible set contains the fixed zero decision. -/
theorem movingDecisions_nonempty (parameter : Decision) :
    (movingDecisions parameter).Nonempty :=
  ⟨zeroDecision, Or.inl rfl⟩

/-- The two-point correspondence has closed graph. -/
theorem movingDecisions_closed_graph : IsClosed (graph movingDecisions) := by
  simpa only [graph, movingDecisions, mem_union, mem_singleton_iff, ofPred_or] using
    (isClosed_eq (continuous_snd : Continuous (Prod.snd : Decision × Decision → Decision))
      (show Continuous (fun _ : Decision × Decision => zeroDecision) from continuous_const)).union
        (isClosed_eq continuous_snd continuous_fst)

/-- Both feasible branches move continuously, so their union is lower hemicontinuous. -/
theorem movingDecisions_lowerHemicontinuous : LowerHemicontinuous movingDecisions := by
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
  intro u hu
  simp only [movingDecisions, union_inter_distrib_right, union_nonempty,
    singleton_inter_nonempty]
  by_cases hzero : zeroDecision ∈ u
  · simpa only [hzero, true_or, ofPred_true] using
      (isOpen_univ : IsOpen (univ : Set Decision))
  · simpa only [hzero, false_or, ofPred_mem_eq] using hu

/-- The feasible sets at zero and one differ: the correspondence is genuinely varying. -/
theorem movingDecisions_vary :
    movingDecisions zeroDecision ≠ movingDecisions ⟨1, by norm_num⟩ := by
  intro heq
  have hmem : (⟨1, by norm_num⟩ : Decision) ∈ movingDecisions zeroDecision :=
    heq ▸ Or.inr rfl
  norm_num [movingDecisions, zeroDecision, Subtype.ext_iff] at hmem

/-- Negative squared distance to a target that moves from minus one to one. -/
def movingPayoff (parameter decision : Decision) : ℝ :=
  -((decision : ℝ) - (2 * (parameter : ℝ) - 1)) ^ 2

private theorem continuous_movingPayoff : Continuous (Function.uncurry movingPayoff) := by
  unfold movingPayoff
  fun_prop

/-- Maximum negative quadratic loss is continuous over the varying feasible sets. -/
theorem moving_quadratic_maximum_continuous :
    Continuous fun parameter : Decision ↦
      sSup (movingPayoff parameter '' movingDecisions parameter) :=
  continuous_sSup_image_of_isClosed_graph movingDecisions movingPayoff
    movingDecisions_nonempty movingDecisions_closed_graph movingDecisions_lowerHemicontinuous
    continuous_movingPayoff

/-- The maximizers for the varying quadratic problem are upper hemicontinuous. -/
theorem moving_quadratic_argmax_upperHemicontinuous :
    UpperHemicontinuous (argmax movingDecisions movingPayoff) :=
  upperHemicontinuous_argmax movingDecisions movingPayoff
    movingDecisions_nonempty movingDecisions_closed_graph movingDecisions_lowerHemicontinuous
    continuous_movingPayoff

/-- Every parameter in the varying quadratic problem has a maximizer. -/
theorem moving_quadratic_argmax_nonempty (parameter : Decision) :
    (argmax movingDecisions movingPayoff parameter).Nonempty :=
  argmax_nonempty movingDecisions movingPayoff
    movingDecisions_nonempty movingDecisions_closed_graph continuous_movingPayoff parameter

/-- The varying quadratic problem has compact optimizer sets. -/
theorem moving_quadratic_argmax_compact (parameter : Decision) :
    IsCompact (argmax movingDecisions movingPayoff parameter) :=
  isCompact_argmax movingDecisions movingPayoff
    movingDecisions_nonempty movingDecisions_closed_graph movingDecisions_lowerHemicontinuous
    continuous_movingPayoff parameter

/-- The zero branch maximizes at one half but ceases to maximize at one. -/
theorem moving_quadratic_argmax_switches :
    zeroDecision ∈ argmax movingDecisions movingPayoff ⟨1 / 2, by norm_num⟩ ∧
      zeroDecision ∉ argmax movingDecisions movingPayoff ⟨1, by norm_num⟩ := by
  norm_num [argmax, movingDecisions, movingPayoff, zeroDecision, image_union, csSup_pair]

/-- An empty feasible set fails the theorem's explicit nonemptiness hypothesis. -/
theorem empty_decisions_fail_nonempty : ¬ (∅ : Set Decision).Nonempty := by
  simp

end BergeMaximum.Examples
