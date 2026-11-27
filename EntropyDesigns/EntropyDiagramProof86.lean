/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof85
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
theorem four_translated_power_strict_local (s : Fin 4 → Bool) {r : ℝ} (hr : 1<r) :
    IsLocalMaxOn (fun q : (Fin 4 → Bool) → ℝ => ∑ x, (q x)^r)
      {q | cubeProbabilityFeasible q} (fourTranslatedLaw s) ∧
    ∃ ε : ℝ, 0<ε ∧ ∀ q : (Fin 4 → Bool) → ℝ,
      cubeProbabilityFeasible q → q≠fourTranslatedLaw s → ‖q-fourTranslatedLaw s‖<ε →
      (∑ x, (q x)^r)<∑ x, (fourTranslatedLaw s x)^r := by
  have hP := (cube_probability_feasible_iff _).mp (four_translated_feasible s)
  have hStrict (z : (Fin 4 → Bool) → ℝ)
      (hz : z∈momentTangentCone (cubeProbabilityMomentMatrix 4) (fourTranslatedLaw s)) (hz0 : z≠0) :
      finitePowerDerivative r (fourTranslatedLaw s) z<0 := by
    rw [finite_power_derivative_apply]
    exact mul_neg_of_pos_of_neg (lt_trans zero_lt_one hr)
      (four_translated_power_gradient_strict s hr z hz hz0)
  obtain ⟨hLocal,ε,hε,hBound⟩ := differentiable_strict_moment_tangent_local
    (cubeProbabilityMomentMatrix 4) (cubeProbabilityMomentTarget 4) (fourTranslatedLaw s) hP
    (fun q : (Fin 4 → Bool) → ℝ => ∑ x, (q x)^r) (finitePowerDerivative r (fourTranslatedLaw s))
    (finite_power_sum_hasFDerivAt hr _) hStrict
  have hSet : {q | feasibleLaw (cubeProbabilityMomentMatrix 4) (cubeProbabilityMomentTarget 4) q}=
      {q : (Fin 4 → Bool) → ℝ | cubeProbabilityFeasible q} := by
    ext q; exact (cube_probability_feasible_iff q).symm
  rw [hSet] at hLocal
  exact ⟨hLocal,ε,hε,fun q hq => hBound q ((cube_probability_feasible_iff q).mp hq)⟩



end
end EntropyDesigns
