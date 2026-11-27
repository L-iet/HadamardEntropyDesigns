/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof62
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
theorem four_entropy_value_comparison_lt_one {α : ℝ} (hPos : 0<α) (hα : α<1) :
    (Real.log 8 ≤ fourWeightedEntropyValue α ↔ fourUniformPowerValue α ≤ fourWeightedPowerValue α) ∧
    (fourWeightedEntropyValue α ≤ Real.log 8 ↔ fourWeightedPowerValue α ≤ fourUniformPowerValue α) := by
  have hU := four_uniform_feasible 0 false
  have hW := four_translated_feasible (fun _ => false)
  constructor
  · have h := renyi_comparison_lt_one (fourUniformLaw 0 false) (fourTranslatedLaw (fun _ => false))
      hU.1 hU.2.1 hW.1 hW.2.1 hα
    simpa only [four_uniform_renyi 0 false hPos,four_weighted_entropy_value _ hPos,
      four_uniform_power_sum 0 false hPos,four_translated_power_sum _ hPos,
      fourUniformPowerValue,fourWeightedPowerValue] using h
  · have h := renyi_comparison_lt_one (fourTranslatedLaw (fun _ => false)) (fourUniformLaw 0 false)
      hW.1 hW.2.1 hU.1 hU.2.1 hα
    simpa only [four_uniform_renyi 0 false hPos,four_weighted_entropy_value _ hPos,
      four_uniform_power_sum 0 false hPos,four_translated_power_sum _ hPos,
      fourUniformPowerValue,fourWeightedPowerValue] using h


end
end EntropyDesigns
