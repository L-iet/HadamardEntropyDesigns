/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof51
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
theorem renyi_comparison_gt_one {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpm : (∑ x, p x)=1)
    (hq : ∀ x, 0 ≤ q x) (hqm : (∑ x, q x)=1) {α : ℝ} (hα : 1<α) :
    finiteRenyi α p ≤ finiteRenyi α q ↔ (∑ x, (q x)^α) ≤ ∑ x, (p x)^α := by
  unfold finiteRenyi
  simp only [if_neg (ne_of_gt hα)]
  have hDen : 1-α= -(α-1) := by ring
  rw [hDen,div_neg,div_neg,neg_le_neg_iff,
    div_le_div_iff_of_pos_right (sub_pos.mpr hα)]
  exact Real.log_le_log_iff (probability_power_sum_pos q hq hqm α)
    (probability_power_sum_pos p hp hpm α)


end
end EntropyDesigns
