/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof22
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
theorem strict_convex_finite_coordinate_sum {α : Type*} [Fintype α] (f : ℝ → ℝ)
    (hf : StrictConvexOn ℝ (Ici 0) f) :
    StrictConvexOn ℝ {p : α → ℝ | ∀ i, 0 ≤ p i} (fun p => ∑ i, f (p i)) := by
  classical
  refine ⟨?_,?_⟩
  · intro p hp q hq a b ha hb _ i
    exact add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hq i))
  · intro p hp q hq hpq a b ha hb hab
    have hNe : ∃ i, p i≠q i := by
      by_contra h
      push Not at h
      exact hpq (funext h)
    obtain ⟨i,hi⟩ := hNe
    have hLe (j : α) : f (a*p j+b*q j) ≤ a*f (p j)+b*f (q j) :=
      hf.convexOn.2 (hp j) (hq j) ha.le hb.le hab
    have hLt : f (a*p i+b*q i) < a*f (p i)+b*f (q i) :=
      hf.2 (hp i) (hq i) hi ha hb hab
    change (∑ j, f (a*p j+b*q j)) < a*(∑ j, f (p j))+b*(∑ j, f (q j))
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_lt_sum (fun j _ => hLe j) ⟨i,Finset.mem_univ i,hLt⟩


end
end EntropyDesigns
