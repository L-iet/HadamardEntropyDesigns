/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof96
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
theorem four_weighted_renyi_continuous_extension :
    Tendsto (fun α : ℝ => (Real.log ((2:ℝ)^α+10)-α*Real.log 12)/(1-α))
      (𝓝[≠] (1:ℝ)) (𝓝 (Real.log 12-Real.log 2/6)) := by
  let g : ℝ → ℝ := fun α => Real.log ((2:ℝ)^α+10)-α*Real.log 12
  have hPow : HasDerivAt (fun α : ℝ => (2:ℝ)^α) (2*Real.log 2) 1 := by
    simpa using (Real.hasStrictDerivAt_const_rpow (by norm_num : (0:ℝ)<2) 1).hasDerivAt
  have hLog := (hPow.add_const 10).log (by norm_num : (2:ℝ)^(1:ℝ)+10≠0)
  have hD : HasDerivAt g (Real.log 2/6-Real.log 12) 1 := by
    have h := hLog.sub ((hasDerivAt_id (1:ℝ)).mul_const (Real.log 12))
    have hFn : ((fun y : ℝ => Real.log ((2:ℝ)^y+10))-(fun y : ℝ => id y*Real.log 12))=g := by
      funext y; rfl
    rw [hFn] at h
    convert h using 1 <;> norm_num <;> ring
  have hG1 : g 1=0 := by norm_num [g]
  have hLimit := hD.tendsto_slope.neg
  have hFn : (fun α : ℝ => -slope g 1 α)=
      (fun α : ℝ => (Real.log ((2:ℝ)^α+10)-α*Real.log 12)/(1-α)) := by
    funext α
    rw [slope_def_field,hG1,sub_zero]
    dsimp [g]
    have hDen : 1-α= -(α-1) := by ring
    rw [hDen,div_neg]
  rw [hFn] at hLimit
  convert hLimit using 1 <;> congr 1 <;> ring


end
end EntropyDesigns
