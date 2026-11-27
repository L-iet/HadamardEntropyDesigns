/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof78
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
theorem four_gradient_dual_value (s x : Fin 4 → Bool) (u v : ℝ) :
    dualMomentValues (cubeProbabilityMomentMatrix 4) (fourGradientDual s u v) x=
      v+(u-v)*(if fourTranslatedWeights s x=1/6 then 1 else
        if fourTranslatedWeights s x=1/12 then 0 else 1/3) := by
  have hC : (∑ r, (fourConstantDual r : ℝ)*cubeProbabilityMomentMatrix 4 r x)=1 := by
    have h := congrArg (fun q : ℚ => (q:ℝ)) (four_constant_dual_certificate x)
    push_cast at h
    simpa only [rationalTrapMomentMatrix_real] using h
  have hQ : (∑ r, (fourQuadraticDual s r : ℝ)*cubeProbabilityMomentMatrix 4 r x)=
      if fourTranslatedWeights s x=1/6 then 1 else if fourTranslatedWeights s x=1/12 then 0 else 1/3 := by
    have hCast (v : ℚ) (hRat : (∑ r, fourQuadraticDual s r*rationalTrapMomentMatrix 4 r x)=v) :
        (∑ r, (fourQuadraticDual s r : ℝ)*cubeProbabilityMomentMatrix 4 r x)=(v:ℝ) := by
      have h := congrArg (fun q : ℚ => (q:ℝ)) hRat
      push_cast at h
      simpa only [rationalTrapMomentMatrix_real] using h
    have hRat := four_quadratic_dual_certificate s x
    split_ifs with h6 h12
    · rw [if_pos h6] at hRat
      convert hCast 1 hRat using 1 <;> norm_num
    · rw [if_neg h6,if_pos h12] at hRat
      convert hCast 0 hRat using 1 <;> norm_num
    · rw [if_neg h6,if_neg h12] at hRat
      convert hCast (1/3) hRat using 1 <;> norm_num
  unfold dualMomentValues fourGradientDual
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,hC,hQ,mul_one]


end
end EntropyDesigns
