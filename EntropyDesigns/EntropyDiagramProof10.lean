/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof09
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
theorem four_parameter_vertex_feasible (a : Fin 5 → ℝ) (ha : a∈fourParameterVertexSet) :
    fourWalshParameterFeasible a := by
  rcases ha with ⟨i,b,rfl⟩|⟨s,hs,hProd,rfl⟩
  · intro v hv _
    have hDot : (∑ j, v j*fourAxisVertex i (bitSign b : ℝ) j)=v i*(bitSign b : ℝ) := by
      simp [fourAxisVertex,mul_ite]
    rw [hDot]
    rcases hv i with h|h <;> rw [h] <;> cases b <;> norm_num [bitSign]
  · intro v hv hp
    have hS (j : Fin 5) : v j*s j=1 ∨ v j*s j= -1 := by
      rcases hv j with h|h <;> rcases hs j with h'|h' <;> rw [h,h'] <;> norm_num
    have hP : (∏ j, v j*s j)=1 := by rw [Finset.prod_mul_distrib,hProd,hp]; norm_num
    have hSum := five_sign_product_one_sum_lower (fun j => v j*s j) hS hP
    have hD : (∑ j, v j*(s j/3))=(∑ j, v j*s j)/3 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hD]
    linarith


end
end EntropyDesigns
