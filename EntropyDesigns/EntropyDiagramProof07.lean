/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof06
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
theorem four_weighted_vertex_decomposition (a s : Fin 5 → ℝ)
    (hs : ∀ i, s i=1 ∨ s i= -1) (hProd : (∏ i, s i)=1)
    (hCoord : ∀ i, s i*|a i|=a i) (m : ℝ) (hm : 0 ≤ m)
    (hMin : ∀ i, m ≤ |a i|) (hMass : (∑ i, |a i|)-2*m ≤ 1) :
    a∈convexHull ℝ fourParameterVertexSet := by
  let w : Fin 6 → ℝ := Fin.cons (3*m) (fun i : Fin 5 => |a i|-m)
  let z : Fin 6 → (Fin 5 → ℝ) := Fin.cons (fun i : Fin 5 => s i/3)
    (fun i : Fin 5 => fourAxisVertex i (s i))
  have hW (i : Fin 6) : 0 ≤ w i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 ≤ 3*m; positivity
    · exact sub_nonneg.mpr (hMin j)
  have hSum : (∑ i, w i) ≤ 1 := by
    dsimp [w]
    norm_num [Fin.sum_univ_succ] at hMass ⊢
    linarith
  have hZ (i : Fin 6) : z i∈convexHull ℝ fourParameterVertexSet := by
    refine Fin.cases ?_ (fun j => ?_) i
    · apply subset_convexHull ℝ fourParameterVertexSet
      right; exact ⟨s,hs,hProd,rfl⟩
    · exact four_axis_vertex_in_hull j (s j) (hs j)
  have h := convex_weighted_sum_le_one (convexHull ℝ fourParameterVertexSet)
    (convex_convexHull ℝ fourParameterVertexSet) four_vertex_zero_in_hull w z hW hSum hZ
  have hEq : (∑ i, w i • z i)=a := by
    ext j
    rw [← hCoord j]
    fin_cases j <;> norm_num [w,z,Fin.sum_univ_succ,fourAxisVertex] <;> ring
  rwa [hEq] at h


end
end EntropyDesigns
