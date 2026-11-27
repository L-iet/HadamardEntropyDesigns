/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof76
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
theorem gradient_dual_interpolation_strict_tangent {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (p g : α → ℝ) (y : ι → ℝ) (L : α → ι → ℝ)
    (hZero : ∀ x, p x=0 → g x=0)
    (hEqual : ∀ x, p x≠0 → dualMomentValues A y x=g x)
    (hOutside : ∀ x, p x=0 → 0<dualMomentValues A y x)
    (hInterpolation : ∀ x, p x≠0 → ∀ t, p t≠0 → (∑ i, L x i*A i t)=if t=x then 1 else 0) :
    ∀ z∈momentTangentCone A p, z≠0 → lawOverlap g z<0 := by
  classical
  intro z hz hz0
  have hTerm (x : α) : 0 ≤ (dualMomentValues A y x-g x)*z x := by
    by_cases hx : p x=0
    · rw [hZero x hx,sub_zero]
      exact mul_nonneg (hOutside x hx).le (hz.2.2 x hx)
    · rw [hEqual x hx,sub_self,zero_mul]
  have hSumNonneg : 0 ≤ ∑ x, (dualMomentValues A y x-g x)*z x :=
    Finset.sum_nonneg (fun x _ => hTerm x)
  have hId := dualMomentValues_pairing A y z
  rw [hz.1] at hId
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hId
  have hGap : (∑ x, (dualMomentValues A y x-g x)*z x)= -lawOverlap g z := by
    simp only [sub_mul,Finset.sum_sub_distrib,hId,zero_sub,lawOverlap]
  by_contra hNot
  have hNonneg : 0 ≤ lawOverlap g z := le_of_not_gt hNot
  have hSumZero : (∑ x, (dualMomentValues A y x-g x)*z x)=0 := by linarith
  have hSupport (x : α) (hx : p x=0) : z x=0 := by
    have hSingle := Finset.single_le_sum (fun t (_ : t∈Finset.univ) => hTerm t) (Finset.mem_univ x)
    rw [hSumZero,hZero x hx,sub_zero] at hSingle
    have hMul : dualMomentValues A y x*z x=0 :=
      le_antisymm hSingle (by simpa only [hZero x hx,sub_zero] using hTerm x)
    exact (mul_eq_zero.mp hMul).resolve_left (hOutside x hx).ne'
  exact hz0 (interpolated_supported_kernel_zero A p L hInterpolation z hz.1 hSupport)


end
end EntropyDesigns
