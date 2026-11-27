/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.PlotkinSupport
open scoped BigOperators

theorem constant_negative_gram_bound {ι α : Type*} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [Fintype α] (v : ι → α → ℝ) (a b : ℝ)
    (hself : ∀ i,∑ j,v i j*v i j=a)
    (hpair : ∀ i l,i≠l → ∑ j,v i j*v l j= -b) :
    (Fintype.card ι : ℝ)*b≤a+b := by
  have hexpand : (∑ j : α,(∑ i : ι,v i j)^2)=
      ∑ i : ι,∑ l : ι,∑ j : α,v i j*v l j := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hrow (i : ι) : (∑ l : ι,∑ j : α,v i j*v l j)=
      a+b-(Fintype.card ι : ℝ)*b := by
    have ht (l : ι) : (∑ j : α,v i j*v l j)= -b+(if l=i then a+b else 0) := by
      by_cases h : l=i
      · subst l
        rw [hself]
        simp
      · rw [hpair i l (Ne.symm h)]
        simp [h]
    simp_rw [ht]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    simp
    ring
  have hnonneg : 0≤∑ j : α,(∑ i : ι,v i j)^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [hexpand] at hnonneg
  simp_rw [hrow] at hnonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hnonneg
  have hq : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  nlinarith

end EntropyDesigns.PlotkinSupport
