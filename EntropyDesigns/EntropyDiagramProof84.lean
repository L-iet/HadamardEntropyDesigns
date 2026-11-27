/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof83
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
theorem finite_power_sum_hasFDerivAt {α : Type*} [Fintype α] {r : ℝ} (hr : 1<r) (p : α → ℝ) :
    HasFDerivAt (fun q : α → ℝ => ∑ x, (q x)^r) (finitePowerDerivative r p) p := by
  classical
  have h (x : α) : HasFDerivAt (fun q : α → ℝ => (q x)^r)
      ((r*(p x)^(r-1)) • (ContinuousLinearMap.proj x : StrongDual ℝ (α → ℝ))) p := by
    let P : StrongDual ℝ (α → ℝ) := ContinuousLinearMap.proj x
    have hP : HasFDerivAt (fun q : α → ℝ => q x) P p := P.hasFDerivAt
    have hh := (Real.hasDerivAt_rpow_const (Or.inr hr.le) (x := p x)).comp_hasFDerivAt p hP
    simpa only [P,Function.comp_def] using hh
  have hSum := HasFDerivAt.sum (fun x (_ : x∈Finset.univ) => h x)
  have hFn : (∑ i : α, fun q : α → ℝ => (q i)^r)=(fun q : α → ℝ => ∑ i, (q i)^r) := by
    funext q
    simp
  rw [hFn] at hSum
  exact hSum


end
end EntropyDesigns
