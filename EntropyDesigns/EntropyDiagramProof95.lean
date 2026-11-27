/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof94
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
theorem power_strict_local_to_cube_renyi {r : ℝ} (hr : 1<r)
    (p : (Fin 4 → Bool) → ℝ)
    (hPower : ∃ ε : ℝ, 0<ε ∧ ∀ q : (Fin 4 → Bool) → ℝ,
      cubeProbabilityFeasible q → q≠p → ‖q-p‖<ε → (∑ x, (q x)^r)<∑ x, (p x)^r) :
    IsStrictCubeRenyiLocalMin r p := by
  obtain ⟨ε,hε,hBound⟩ := hPower
  have hStrict (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) (hqp : q≠p)
      (hClose : ‖q-p‖<ε) : finiteRenyi r p<finiteRenyi r q :=
    renyi_lt_of_power_sum_lt p q hq.1 hq.2.1 hr (hBound q hq hqp hClose)
  refine ⟨?_,ε,hε,hStrict⟩
  have hBall : ∀ᶠ q : (Fin 4 → Bool) → ℝ in 𝓝 p, ‖q-p‖<ε := by
    simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds p hε
  have hMem : ∀ᶠ q : (Fin 4 → Bool) → ℝ in 𝓝[{q | cubeProbabilityFeasible q}] p,
      cubeProbabilityFeasible q := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds hBall,hMem] with q hClose hq
  by_cases hqp : q=p
  · subst q; exact le_rfl
  · exact (hStrict q hq hqp hClose).le


end
end EntropyDesigns
