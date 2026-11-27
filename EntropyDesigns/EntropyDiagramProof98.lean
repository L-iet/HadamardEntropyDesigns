/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof97
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
theorem four_bit_complete_entropy_diagram :
    ∃ τ : ℝ, 6<τ ∧ τ<7 ∧ entropyTransitionPhi τ=0 ∧
      (∀ β : ℝ, 1<β → entropyTransitionPhi β=0 → β=τ) ∧
      (∀ α : ℝ, 0<α → ∀ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q →
        (IsCubeRenyiGlobalMin α q ↔
          if α<τ then fourUniformFamily q else if τ<α then fourWeightedFamily q else
            fourUniformFamily q ∨ fourWeightedFamily q)) ∧
      (∀ α : ℝ, 0<α → ∃ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q ∧
        finiteRenyi α q=min (Real.log 8) (fourWeightedEntropyValue α) ∧ IsCubeRenyiGlobalMin α q) ∧
      (∀ r : ℝ, 1<r →
        (∀ (i : Fin 5) (b : Bool), IsStrictCubeRenyiLocalMin r (fourUniformLaw i b)) ∧
        (∀ s : Fin 4 → Bool, IsStrictCubeRenyiLocalMin r (fourTranslatedLaw s))) ∧
      Tendsto (fun α : ℝ => (Real.log ((2:ℝ)^α+10)-α*Real.log 12)/(1-α))
        (𝓝[≠] (1:ℝ)) (𝓝 (Real.log 12-Real.log 2/6)) := by
  obtain ⟨τ,h6,h7,hRoot,hUnique,hPhase⟩ := four_bit_entropy_global_phase
  refine ⟨τ,h6,h7,hRoot,hUnique,hPhase,?_,?_,four_weighted_renyi_continuous_extension⟩
  · intro α hα
    exact four_renyi_minimum_value hα
  · intro r hr
    exact four_bit_renyi_local_persistence hr


end
end EntropyDesigns
