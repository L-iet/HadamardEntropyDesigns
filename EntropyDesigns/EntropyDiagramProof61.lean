/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof60
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
theorem four_renyi_minimizers_values {α : ℝ} (hα : 0<α)
    (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) :
    (∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → finiteRenyi α q ≤ finiteRenyi α v) ↔
      (∃ (i : Fin 5) (b : Bool), q=fourUniformLaw i b ∧ Real.log 8 ≤ fourWeightedEntropyValue α) ∨
      (∃ s : Fin 4 → Bool, q=fourTranslatedLaw s ∧ fourWeightedEntropyValue α ≤ Real.log 8) := by
  rcases lt_trichotomy α 1 with hLt|hEq|hGt
  · apply four_order_reversing_objective_minimizers
      (fun p : (Fin 4 → Bool) → ℝ => -(∑ x, (p x)^α)) (finiteRenyi α)
      (finite_negative_power_sum_strict_convex hα hLt)
      (-fourUniformPowerValue α) (-fourWeightedPowerValue α) (Real.log 8) (fourWeightedEntropyValue α)
    · intro i b; rw [four_uniform_power_sum i b hα]; rfl
    · intro s; rw [four_translated_power_sum s hα]; rfl
    · exact fun i b => four_uniform_renyi i b hα
    · exact fun s => four_weighted_entropy_value s hα
    · intro p v hp hv
      simpa only [neg_le_neg_iff] using renyi_comparison_lt_one p v hp.1 hp.2.1 hv.1 hv.2.1 hLt
    · exact hq
  · subst α
    apply four_order_reversing_objective_minimizers
      (fun p : (Fin 4 → Bool) → ℝ => ∑ x, p x*Real.log (p x)) (finiteRenyi 1)
      finite_negative_shannon_strict_convex
      (-Real.log 8) (-(Real.log 12-Real.log 2/6)) (Real.log 8) (fourWeightedEntropyValue 1)
    · intro i b; have h := four_uniform_shannon i b; unfold shannon at h; linarith
    · intro s; have h := four_translated_shannon s; unfold shannon at h; linarith
    · exact fun i b => four_uniform_renyi i b (by norm_num)
    · exact fun s => four_weighted_entropy_value s (by norm_num)
    · intro p v _ _
      simp only [finiteRenyi,ite_true,shannon,neg_le_neg_iff]
    · exact hq
  · apply four_order_reversing_objective_minimizers
      (fun p : (Fin 4 → Bool) → ℝ => ∑ x, (p x)^α) (finiteRenyi α)
      (finite_power_sum_strict_convex hGt)
      (fourUniformPowerValue α) (fourWeightedPowerValue α) (Real.log 8) (fourWeightedEntropyValue α)
    · intro i b; exact four_uniform_power_sum i b hα
    · intro s; exact four_translated_power_sum s hα
    · exact fun i b => four_uniform_renyi i b hα
    · exact fun s => four_weighted_entropy_value s hα
    · intro p v hp hv
      exact renyi_comparison_gt_one p v hp.1 hp.2.1 hv.1 hv.2.1 hGt
    · exact hq


end
end EntropyDesigns
