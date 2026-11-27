/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof55
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
theorem four_weighted_renyi (s : Fin 4 → Bool) {α : ℝ} (hα : 0<α) (hOne : α≠1) :
    finiteRenyi α (fourTranslatedLaw s)=
      (Real.log ((2:ℝ)^α+10)-α*Real.log 12)/(1-α) := by
  rw [finiteRenyi,if_neg hOne,four_translated_power_sum s hα]
  change Real.log (fourWeightedPowerValue α)/(1-α)=_
  rw [four_weighted_power_value_factorization]
  have hPos : 0<(2:ℝ)^α+10 := by positivity
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<1/12) α))
      (ne_of_gt hPos),Real.log_rpow (by norm_num : (0:ℝ)<1/12) α]
  have hInv : Real.log (1/12:ℝ)= -Real.log 12 := by simp [one_div,Real.log_inv]
  rw [hInv]
  ring


end
end EntropyDesigns
