/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof63
public import EntropyDesigns.FourBitEscape
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.Order.IntermediateValue
set_option Elab.async false
@[expose] public section
set_option maxHeartbeats 4000000
namespace EntropyDesigns
open Set
noncomputable section

open Filter
open scoped Topology
theorem four_entropy_value_phase {τ : ℝ} (hτ : 1<τ) (hRoot : entropyTransitionPhi τ=0)
    {α : ℝ} (hPos : 0<α) :
    (α<τ → Real.log 8<fourWeightedEntropyValue α) ∧
    (α=τ → Real.log 8=fourWeightedEntropyValue α) ∧
    (τ<α → fourWeightedEntropyValue α<Real.log 8) := by
  have hSign := entropy_transition_sign_diagram hτ hRoot
  have hPow : 0<(1/8:ℝ)^α := Real.rpow_pos_of_pos (by norm_num) α
  have hDiff := four_power_value_difference α
  rcases lt_trichotomy α 1 with hLt|hEq|hGt
  · have hφ := hSign.1 α hLt
    have hUW : fourUniformPowerValue α<fourWeightedPowerValue α := by
      nlinarith [mul_pos hPow hφ]
    have hCmp := four_entropy_value_comparison_lt_one hPos hLt
    have hStrict : Real.log 8<fourWeightedEntropyValue α :=
      lt_of_not_ge (fun h => not_le_of_gt hUW (hCmp.2.mp h))
    exact ⟨fun _ => hStrict,fun h => False.elim (by linarith),fun h => False.elim (by linarith)⟩
  · subst α
    have hStrict : Real.log 8<fourWeightedEntropyValue 1 := by
      simpa only [fourWeightedEntropyValue,ite_true] using four_shannon_values_strict
    exact ⟨fun _ => hStrict,fun h => False.elim (by linarith),fun h => False.elim (by linarith)⟩
  · have hCmp := four_entropy_value_comparison_gt_one hGt
    refine ⟨?_,?_,?_⟩
    · intro hατ
      have hφ := hSign.2.1 α hGt hατ
      have hWU : fourWeightedPowerValue α<fourUniformPowerValue α := by
        nlinarith [mul_neg_of_pos_of_neg hPow hφ]
      exact lt_of_not_ge (fun h => not_le_of_gt hWU (hCmp.2.mp h))
    · intro hατ
      have hφ : entropyTransitionPhi α=0 := by rw [hατ]; exact hRoot
      have hEq : fourWeightedPowerValue α=fourUniformPowerValue α := by rw [hφ,mul_zero] at hDiff; linarith
      exact le_antisymm (hCmp.1.mpr hEq.le) (hCmp.2.mpr hEq.ge)
    · intro hτα
      have hφ := hSign.2.2 α hτα
      have hUW : fourUniformPowerValue α<fourWeightedPowerValue α := by
        nlinarith [mul_pos hPow hφ]
      exact lt_of_not_ge (fun h => not_le_of_gt hUW (hCmp.1.mp h))


end
end EntropyDesigns
