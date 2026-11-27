/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof48
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
theorem four_translated_shannon (s : Fin 4 → Bool) :
    shannon (fourTranslatedLaw s)=Real.log 12-Real.log 2/6 := by
  have h := four_translated_function_sum s (fun r => (r:ℝ)*Real.log (r:ℝ))
  norm_num at h
  have h12 : Real.log (12:ℝ)=Real.log 2+Real.log 6 := by
    have hh := Real.log_mul (by norm_num : (2:ℝ)≠0) (by norm_num : (6:ℝ)≠0)
    norm_num at hh
    exact hh
  have h6inv : Real.log (1/6:ℝ)= -Real.log 6 := by simp [one_div,Real.log_inv]
  have h12inv : Real.log (1/12:ℝ)= -Real.log 12 := by simp [one_div,Real.log_inv]
  rw [h6inv,h12inv] at h
  unfold shannon
  change -(∑ x, (fourTranslatedWeights s x:ℝ)*Real.log (fourTranslatedWeights s x:ℝ))=_
  rw [h]
  linarith


end
end EntropyDesigns
