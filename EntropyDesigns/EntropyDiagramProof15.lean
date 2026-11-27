/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof14
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
theorem four_parameter_law_coefficients (a : Fin 5 → ℝ) (j : Fin 5) :
    fourWalshCoefficients (fourParameterLaw a) j=a j := by
  have hMean : (∑ x, (fourHighCharacter j x : ℝ))=0 := by
    exact_mod_cast four_high_character_certificate.1 j
  have hGram (i : Fin 5) :
      (∑ x, (fourHighCharacter i x : ℝ)*(fourHighCharacter j x : ℝ))=
        if i=j then (16:ℝ) else 0 := by
    have h := congrArg (fun n : ℤ => (n:ℝ)) (four_high_character_certificate.2.2.2.1 i j)
    push_cast at h
    by_cases hij : i=j <;> simp [hij] at h ⊢ <;> exact h
  have hPoint (x : Fin 4 → Bool) : fourParameterLaw a x*(fourHighCharacter j x : ℝ)=
      ((fourHighCharacter j x : ℝ)+∑ i, a i*((fourHighCharacter i x : ℝ)*(fourHighCharacter j x : ℝ)))/16 := by
    unfold fourParameterLaw
    have hS : (∑ i, a i*(fourHighCharacter i x : ℝ))*(fourHighCharacter j x : ℝ)=
        ∑ i, a i*((fourHighCharacter i x : ℝ)*(fourHighCharacter j x : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [← hS]
    ring
  unfold fourWalshCoefficients
  simp_rw [hPoint]
  rw [← Finset.sum_div,Finset.sum_add_distrib,hMean,zero_add,Finset.sum_comm]
  have hS (i : Fin 5) : (∑ x, a i*((fourHighCharacter i x : ℝ)*(fourHighCharacter j x : ℝ)))=
      a i*(if i=j then (16:ℝ) else 0) := by rw [← Finset.mul_sum,hGram]
  simp only [hS,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring


end
end EntropyDesigns
