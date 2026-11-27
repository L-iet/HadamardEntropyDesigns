/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof36
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
theorem entropy_transition_unique_root :
    ∃ α : ℝ, 6<α ∧ α<7 ∧ entropyTransitionPhi α=0 ∧
      ∀ β : ℝ, entropyTransitionPhi β=0 → β=1 ∨ β=α := by
  have hc : Continuous entropyTransitionPhi := by unfold entropyTransitionPhi; fun_prop
  have hv := entropy_transition_values
  have hZero : (0:ℝ) ∈ Set.Icc (entropyTransitionPhi 6) (entropyTransitionPhi 7) := ⟨hv.2.1.le,hv.2.2.le⟩
  obtain ⟨α,hα,hRoot⟩ := intermediate_value_Icc (by norm_num : (6:ℝ)≤7) hc.continuousOn hZero
  have h6 : 6<α := lt_of_le_of_ne hα.1 (by intro h; subst α; linarith)
  have h7 : α<7 := lt_of_le_of_ne hα.2 (by intro h; subst α; linarith)
  have hThree (x y z : ℝ) (hxy : x<y) (hyz : y<z)
      (hx : entropyTransitionPhi x=0) (hy : entropyTransitionPhi y=0)
      (hz : entropyTransitionPhi z=0) : False := by
    have hSeg : y∈openSegment ℝ x z := by
      rw [openSegment_eq_Ioo (lt_trans hxy hyz)]; exact ⟨hxy,hyz⟩
    have h := entropy_transition_strict_convex.lt_on_openSegment
      (Set.mem_univ x) (Set.mem_univ z) (ne_of_lt (lt_trans hxy hyz)) hSeg
    rw [hx,hy,hz,max_self] at h
    exact (lt_irrefl 0) h
  refine ⟨α,h6,h7,hRoot,?_⟩
  intro β hβ
  rcases lt_trichotomy β 1 with hβ1|hβ1|hβ1
  · exact False.elim (hThree β 1 α hβ1 (by linarith) hβ hv.1 hRoot)
  · exact Or.inl hβ1
  · rcases lt_trichotomy β α with hβα|hβα|hβα
    · exact False.elim (hThree 1 β α hβ1 hβα hv.1 hβ hRoot)
    · exact Or.inr hβα
    · exact False.elim (hThree 1 α β (by linarith) hβα hv.1 hRoot hβ)


end
end EntropyDesigns
