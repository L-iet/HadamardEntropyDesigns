/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof64
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
theorem four_renyi_minimum_value {α : ℝ} (hα : 0<α) :
    ∃ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q ∧
      finiteRenyi α q=min (Real.log 8) (fourWeightedEntropyValue α) ∧
      ∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → finiteRenyi α q ≤ finiteRenyi α v := by
  by_cases hLe : Real.log 8 ≤ fourWeightedEntropyValue α
  · refine ⟨fourUniformLaw 0 false,four_uniform_feasible 0 false,?_,?_⟩
    · rw [four_uniform_renyi 0 false hα,min_eq_left hLe]
    · apply (four_renyi_minimizers_values hα _ (four_uniform_feasible 0 false)).mpr
      exact Or.inl ⟨0,false,rfl,hLe⟩
  · have hLe' := le_of_not_ge hLe
    refine ⟨fourTranslatedLaw (fun _ => false),four_translated_feasible _,?_,?_⟩
    · rw [four_weighted_entropy_value _ hα,min_eq_right hLe']
    · apply (four_renyi_minimizers_values hα _ (four_translated_feasible _)).mpr
      exact Or.inr ⟨_,rfl,hLe'⟩


end
end EntropyDesigns
