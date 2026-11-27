/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof07
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
theorem four_parameter_mem_vertex_hull (a : Fin 5 → ℝ) (ha : fourWalshParameterFeasible a) :
    a∈convexHull ℝ fourParameterVertexSet := by
  classical
  obtain ⟨s,hs,hAbs,hCoord,hProd⟩ := four_signed_absolute_coordinates a
  rcases hProd with hProd|hProd
  · obtain ⟨j,hj,hMin⟩ := (Finset.univ : Finset (Fin 5)).exists_min_image (fun i => |a i|) Finset.univ_nonempty
    have hBound := four_parameter_slack_nonnegative s hs hProd a ha j
    have hB : 0 ≤ 1+2*(s j*a j)-(∑ k, s k*a k) := by linarith
    simp only [hAbs] at hB
    exact four_weighted_vertex_decomposition a s hs hProd hCoord |a j| (abs_nonneg _)
      (fun i => hMin i (Finset.mem_univ i)) (by linarith)
  · have hSigns (j : Fin 5) : -s j=1 ∨ -s j= -1 := by
      rcases hs j with h|h <;> rw [h] <;> norm_num
    have hP : (∏ j, -s j)=1 := by norm_num [Finset.prod_neg,hProd]
    have h := ha (fun j => -s j) hSigns hP
    have hDot : (∑ j, -s j*a j)= -(∑ j, |a j|) := by
      simp only [neg_mul,hAbs,Finset.sum_neg_distrib]
    rw [hDot] at h
    exact four_signed_axis_decomposition a s hs hCoord (by linarith)


end
end EntropyDesigns
