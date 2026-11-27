/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourTranslatedFinite
public import EntropyDesigns.NonuniformTraps
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
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
noncomputable def fourWalshCoefficients (q : (Fin 4 → Bool) → ℝ) (i : Fin 5) : ℝ :=
  ∑ x, q x*(fourHighCharacter i x : ℝ)

theorem four_low_kernel_expectation (q : (Fin 4 → Bool) → ℝ)
    (hq : cubeProbabilityFeasible q) (x : Fin 4 → Bool) :
    (∑ y, q y*(fourLowKernel x y : ℝ))=1 := by
  rcases hq with ⟨_,hm,hi,hij⟩
  simp only [fourLowKernel, Int.cast_add, Int.cast_one, Int.cast_sum,
    Int.cast_mul, Int.cast_ite, Int.cast_zero, mul_add, mul_one,
    Finset.sum_add_distrib, hm]
  have hs : (∑ y, q y*∑ i : Fin 4, (bitSign (x i) : ℝ)*(bitSign (y i) : ℝ))=0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h (i : Fin 4) : (∑ y, q y*((bitSign (x i) : ℝ)*(bitSign (y i) : ℝ)))=0 := by
      calc
        _=(bitSign (x i) : ℝ)*(∑ y, q y*(bitSign (y i) : ℝ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
        _=0 := by rw [hi]; ring
    simp only [h,Finset.sum_const_zero]
  rw [hs,add_zero]
  have h (ij : Fin 4×Fin 4) :
      (∑ y, q y*(if ij.1 < ij.2 then
        (bitSign (x ij.1) : ℝ)*(bitSign (x ij.2) : ℝ)*
        (bitSign (y ij.1) : ℝ)*(bitSign (y ij.2) : ℝ) else 0))=0 := by
    split_ifs with hlt
    · calc
        _=((bitSign (x ij.1) : ℝ)*(bitSign (x ij.2) : ℝ))*
            (∑ y, q y*(bitSign (y ij.1) : ℝ)*(bitSign (y ij.2) : ℝ)) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
        _=0 := by rw [hij _ _ (ne_of_lt hlt)]; ring
    · simp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [h,Finset.sum_const_zero,add_zero]

theorem four_walsh_reconstruction (q : (Fin 4 → Bool) → ℝ)
    (hq : cubeProbabilityFeasible q) (x : Fin 4 → Bool) :
    16*q x=1+∑ i : Fin 5, fourWalshCoefficients q i*(fourHighCharacter i x : ℝ) := by
  have hK (y : Fin 4 → Bool) :
      (16:ℝ)*(if y=x then 1 else 0)=(fourLowKernel x y : ℝ)+
        ∑ i : Fin 5, (fourHighCharacter i x : ℝ)*(fourHighCharacter i y : ℝ) := by
    exact_mod_cast four_walsh_kernel_certificate x y
  calc
    16*q x=(∑ y, q y*((16:ℝ)*(if y=x then 1 else 0))) := by
      simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      ring
    _=(∑ y, q y*(fourLowKernel x y : ℝ))+
        ∑ y, q y*(∑ i : Fin 5, (fourHighCharacter i x : ℝ)*(fourHighCharacter i y : ℝ)) := by
      simp_rw [hK,mul_add,Finset.sum_add_distrib]
    _=1+∑ i : Fin 5, fourWalshCoefficients q i*(fourHighCharacter i x : ℝ) := by
      rw [four_low_kernel_expectation q hq x]
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      unfold fourWalshCoefficients
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring



end EntropyDesigns
