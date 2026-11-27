/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof30
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
theorem four_objective_upper_bound (f : ((Fin 4 → Bool) → ℝ) → ℝ)
    (hf : StrictConvexOn ℝ {p : (Fin 4 → Bool) → ℝ | ∀ x, 0 ≤ p x} f)
    (U W : ℝ) (hU : ∀ i b, f (fourUniformLaw i b)=U)
    (hW : ∀ s, f (fourTranslatedLaw s)=W)
    (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) : f q ≤ max U W := by
  have hStrict := four_objective_strict_convex f hf
  have hConvex := hStrict.convexOn.convex_le (max U W)
  have hVertex : fourParameterVertexSet ⊆
      {a : Fin 5 → ℝ | fourWalshParameterFeasible a ∧ f (fourParameterLaw a) ≤ max U W} := by
    intro a ha
    refine ⟨four_parameter_vertex_feasible a ha,?_⟩
    rcases ha with ⟨i,b,rfl⟩|⟨s,hs,hProd,rfl⟩
    · rw [four_axis_vertex_law,hU]; exact le_max_left U W
    · obtain ⟨u,hu⟩ := four_weighted_vertex_law s hs hProd
      rw [hu,hW]; exact le_max_right U W
  have hHull := convexHull_min hVertex hConvex
  have hIn := hHull (four_parameter_mem_vertex_hull (fourWalshCoefficients q) (four_coefficients_feasible q hq))
  change fourWalshParameterFeasible (fourWalshCoefficients q) ∧ f (fourParameterLaw (fourWalshCoefficients q)) ≤ max U W at hIn
  rw [four_parameter_law_reconstruct q hq] at hIn
  exact hIn.2


end
end EntropyDesigns
