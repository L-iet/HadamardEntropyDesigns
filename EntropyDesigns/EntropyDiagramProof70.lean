/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof69
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
theorem four_bit_entropy_global_phase :
    ∃ τ : ℝ, 6<τ ∧ τ<7 ∧ entropyTransitionPhi τ=0 ∧
      (∀ β : ℝ, 1<β → entropyTransitionPhi β=0 → β=τ) ∧
      ∀ α : ℝ, 0<α → ∀ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q →
        (IsCubeRenyiGlobalMin α q ↔
          if α<τ then fourUniformFamily q else if τ<α then fourWeightedFamily q else
            fourUniformFamily q ∨ fourWeightedFamily q) := by
  obtain ⟨τ,h6,h7,hRoot,hOnly⟩ := entropy_transition_unique_root
  refine ⟨τ,h6,h7,hRoot,?_,?_⟩
  · intro β hβ hZero
    rcases hOnly β hZero with hOne|hτ
    · exact False.elim (by linarith)
    · exact hτ
  · intro α hα q hq
    exact four_renyi_phase_selector (by linarith) hRoot hα q hq




end
end EntropyDesigns
