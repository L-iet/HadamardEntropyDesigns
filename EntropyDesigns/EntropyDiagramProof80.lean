/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof79
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
theorem four_translated_interpolation_real (s x t : Fin 4 → Bool)
    (hx : fourTranslatedLaw s x≠0) (ht : fourTranslatedLaw s t≠0) :
    (∑ r, (fourTranslatedInterpolation s x r : ℝ)*cubeProbabilityMomentMatrix 4 r t)=
      if t=x then 1 else 0 := by
  have hxQ : fourTranslatedWeights s x≠0 := by
    change (fourTranslatedWeights s x : ℝ)≠0 at hx
    exact_mod_cast hx
  have htQ : fourTranslatedWeights s t≠0 := by
    change (fourTranslatedWeights s t : ℝ)≠0 at ht
    exact_mod_cast ht
  have h := congrArg (fun q : ℚ => (q:ℝ)) (four_gradient_interpolation_certificate s x t hxQ htQ)
  push_cast at h
  simp only [rationalTrapMomentMatrix_real] at h
  by_cases hxt : t=x <;> simp [hxt] at h ⊢ <;> exact h


end
end EntropyDesigns
