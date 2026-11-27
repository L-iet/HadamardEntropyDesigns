/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof37
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
theorem entropy_transition_sign_diagram {α : ℝ} (hα : 1<α)
    (hRoot : entropyTransitionPhi α=0) :
    (∀ β : ℝ, β<1 → 0<entropyTransitionPhi β) ∧
    (∀ β : ℝ, 1<β → β<α → entropyTransitionPhi β<0) ∧
    (∀ β : ℝ, α<β → 0<entropyTransitionPhi β) := by
  have hOne := entropy_transition_values.1
  refine ⟨?_,?_,?_⟩
  · intro β hβ
    by_contra hNot
    have hLe := le_of_not_gt hNot
    have hSeg : (1:ℝ)∈openSegment ℝ β α := by
      rw [openSegment_eq_Ioo (lt_trans hβ hα)]; exact ⟨hβ,hα⟩
    have h := entropy_transition_strict_convex.lt_on_openSegment
      (Set.mem_univ β) (Set.mem_univ α) (ne_of_lt (lt_trans hβ hα)) hSeg
    rw [hOne,hRoot] at h
    have hMax : max (entropyTransitionPhi β) 0 ≤ 0 := max_le hLe le_rfl
    linarith
  · intro β hβ hβα
    have hSeg : β∈openSegment ℝ 1 α := by rw [openSegment_eq_Ioo hα]; exact ⟨hβ,hβα⟩
    have h := entropy_transition_strict_convex.lt_on_openSegment
      (Set.mem_univ 1) (Set.mem_univ α) (ne_of_lt hα) hSeg
    simpa only [hOne,hRoot,max_self] using h
  · intro β hβ
    by_contra hNot
    have hLe := le_of_not_gt hNot
    have hSeg : α∈openSegment ℝ 1 β := by
      rw [openSegment_eq_Ioo (lt_trans hα hβ)]; exact ⟨hα,hβ⟩
    have h := entropy_transition_strict_convex.lt_on_openSegment
      (Set.mem_univ 1) (Set.mem_univ β) (ne_of_lt (lt_trans hα hβ)) hSeg
    rw [hOne,hRoot] at h
    have hMax : max 0 (entropyTransitionPhi β) ≤ 0 := max_le le_rfl hLe
    linarith



end
end EntropyDesigns
