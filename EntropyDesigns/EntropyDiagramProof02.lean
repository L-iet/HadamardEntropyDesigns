/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof01
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
theorem convex_weighted_sum_le_one {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype ι] (S : Set E) (hS : Convex ℝ S) (hZero : (0:E)∈S)
    (w : ι → ℝ) (z : ι → E) (hw : ∀ i, 0 ≤ w i) (hMass : (∑ i, w i) ≤ 1)
    (hz : ∀ i, z i∈S) : (∑ i, w i • z i)∈S := by
  classical
  let W : Option ι → ℝ := fun i => i.elim (1-∑ j,w j) w
  let Z : Option ι → E := fun i => i.elim 0 z
  have hW (i : Option ι) : 0 ≤ W i := by
    cases i with
    | none => exact sub_nonneg.mpr hMass
    | some i => exact hw i
  have hSum : (∑ i : Option ι, W i)=1 := by simp [W,Fintype.sum_option]
  have hZ (i : Option ι) : Z i∈S := by
    cases i with
    | none => exact hZero
    | some i => exact hz i
  have h := hS.sum_mem (fun i (_ : i∈Finset.univ) => hW i) hSum
    (fun i (_ : i∈Finset.univ) => hZ i)
  simpa [W,Z,Fintype.sum_option] using h


end
end EntropyDesigns
