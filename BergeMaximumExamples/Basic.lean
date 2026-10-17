/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import BergeMaximum
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Parametric quadratic optimization on a compact interval

Berge semicontinuity applies to the genuine bounded quadratic optimization problem.
It does not assert a full continuity theorem from closed graph alone.
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
  · exact fun _ ↦ isClosed_univ
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
  · exact fun _ ↦ isClosed_univ
  · exact fun _ ↦ ⟨⟨0, by norm_num⟩, mem_univ _⟩
  · simpa only [graph, mem_univ, ofPred_true] using
      (isClosed_univ : IsClosed (univ : Set (ℝ × Decision)))
  · exact (by fun_prop : Continuous
      (Function.uncurry fun parameter : ℝ ↦
        fun decision : Decision ↦ (parameter - (decision : ℝ)) ^ 2)).upperSemicontinuous

/-- An empty feasible set fails the theorem's explicit nonemptiness hypothesis. -/
theorem empty_decisions_fail_nonempty : ¬ (∅ : Set Decision).Nonempty := by
  simp

end BergeMaximum.Examples
