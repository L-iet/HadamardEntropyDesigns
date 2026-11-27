/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof20
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
theorem four_parameter_law_feasible (a : Fin 5 → ℝ) (ha : fourWalshParameterFeasible a) :
    cubeProbabilityFeasible (fourParameterLaw a) := by
  have hVertex (v : Fin 5 → ℝ) (hv : v∈fourParameterVertexSet) :
      cubeProbabilityFeasible (fourParameterLaw v) := by
    rcases hv with ⟨i,b,rfl⟩|⟨s,hs,hProd,rfl⟩
    · rw [four_axis_vertex_law]; exact four_uniform_feasible i b
    · obtain ⟨u,hu⟩ := four_weighted_vertex_law s hs hProd
      rw [hu]; exact four_translated_feasible u
  have hConvex : Convex ℝ {v : Fin 5 → ℝ | cubeProbabilityFeasible (fourParameterLaw v)} := by
    intro x hx y hy u v hu hv huv
    change cubeProbabilityFeasible (fourParameterLaw (u • x+v • y))
    rw [four_parameter_law_affine x y u v huv]
    have huEq : u=1-v := by linarith
    rw [huEq]
    exact cube_probability_feasible_segment hx hy hv (by linarith)
  exact (convexHull_min hVertex hConvex) (four_parameter_mem_vertex_hull a ha)


end
end EntropyDesigns
