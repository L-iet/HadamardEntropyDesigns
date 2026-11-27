/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof02
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
theorem four_vertex_zero_in_hull : (0 : Fin 5 → ℝ)∈convexHull ℝ fourParameterVertexSet := by
  have hp : fourAxisVertex 0 1∈fourParameterVertexSet := Or.inl ⟨0,false,by simp [bitSign]⟩
  have hm : fourAxisVertex 0 (-1)∈fourParameterVertexSet := Or.inl ⟨0,true,by simp [bitSign]⟩
  have h := (convex_convexHull ℝ fourParameterVertexSet)
    (subset_convexHull ℝ fourParameterVertexSet hp) (subset_convexHull ℝ fourParameterVertexSet hm)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  have hEq : (1/2:ℝ) • fourAxisVertex 0 1+(1/2:ℝ) • fourAxisVertex 0 (-1)=0 := by
    ext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,fourAxisVertex,Pi.zero_apply]
    split_ifs <;> ring
  rwa [hEq] at h


end
end EntropyDesigns
