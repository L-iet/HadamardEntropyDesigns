/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof41
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
theorem four_uniform_function_sum (i : Fin 5) (b : Bool) (f : ℚ → ℝ) :
    (∑ x, f (fourUniformWeights i b x))=8*f 0+8*f (1/8) := by
  classical
  have h := four_uniform_weight_profile_certificate i b
  have hPoint (x : Fin 4 → Bool) : f (fourUniformWeights i b x)=
      (if fourUniformWeights i b x=0 then f 0 else 0)+
      (if fourUniformWeights i b x=1/8 then f (1/8) else 0) := by
    rcases h.1 x with hx|hx <;> rw [hx] <;> norm_num
  simp_rw [hPoint,Finset.sum_add_distrib]
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul]
  rw [h.2.1,h.2.2]
  norm_num


end
end EntropyDesigns
