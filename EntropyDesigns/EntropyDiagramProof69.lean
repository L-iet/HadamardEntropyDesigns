/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof68
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
theorem four_renyi_phase_selector {τ : ℝ} (hτ : 1<τ) (hRoot : entropyTransitionPhi τ=0)
    {α : ℝ} (hα : 0<α) (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) :
    IsCubeRenyiGlobalMin α q ↔
      if α<τ then fourUniformFamily q else if τ<α then fourWeightedFamily q else
        fourUniformFamily q ∨ fourWeightedFamily q := by
  rw [IsCubeRenyiGlobalMin,four_renyi_minimizers_values hα q hq]
  have hPhase := four_entropy_value_phase hτ hRoot hα
  by_cases hLt : α<τ
  · rw [if_pos hLt]
    have hStrict := hPhase.1 hLt
    constructor
    · rintro (⟨i,b,hEq,_⟩|⟨s,hEq,hBad⟩)
      · exact ⟨i,b,hEq⟩
      · exact False.elim (not_le_of_gt hStrict hBad)
    · rintro ⟨i,b,hEq⟩
      exact Or.inl ⟨i,b,hEq,hStrict.le⟩
  · rw [if_neg hLt]
    by_cases hGt : τ<α
    · rw [if_pos hGt]
      have hStrict := hPhase.2.2 hGt
      constructor
      · rintro (⟨i,b,hEq,hBad⟩|⟨s,hEq,_⟩)
        · exact False.elim (not_le_of_gt hStrict hBad)
        · exact ⟨s,hEq⟩
      · rintro ⟨s,hEq⟩
        exact Or.inr ⟨s,hEq,hStrict.le⟩
    · rw [if_neg hGt]
      have hEq : α=τ := by linarith
      have hValues := hPhase.2.1 hEq
      constructor
      · rintro (⟨i,b,hModel,_⟩|⟨s,hModel,_⟩)
        · exact Or.inl ⟨i,b,hModel⟩
        · exact Or.inr ⟨s,hModel⟩
      · rintro (⟨i,b,hModel⟩|⟨s,hModel⟩)
        · exact Or.inl ⟨i,b,hModel,hValues.le⟩
        · exact Or.inr ⟨s,hModel,hValues.ge⟩


end
end EntropyDesigns
