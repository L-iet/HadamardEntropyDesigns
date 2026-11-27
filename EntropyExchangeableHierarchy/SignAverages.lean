/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
open scoped BigOperators

def randomSign {A : Type*} (ε : A → Bool) (i : A) : ℝ := if ε i then -1 else 1

theorem randomSign_mul_self {A : Type*} (ε : A → Bool) (i : A) :
    randomSign ε i*randomSign ε i=1 := by
  cases hi : ε i <;> norm_num [randomSign,hi]

def flipSignAt {A : Type*} [DecidableEq A] (i : A) (ε : A → Bool) : A → Bool :=
  fun j => if j=i then !(ε j) else ε j

theorem flipSignAt_involutive {A : Type*} [DecidableEq A] (i : A) :
    Function.Involutive (flipSignAt i) := by
  intro ε
  funext j
  by_cases hj : j=i <;> simp [flipSignAt,hj]

def flipSignEquiv {A : Type*} [DecidableEq A] (i : A) : (A → Bool) ≃ (A → Bool) :=
  Function.Involutive.toPerm (flipSignAt i) (flipSignAt_involutive i)

theorem randomSign_flip_self {A : Type*} [DecidableEq A] (i : A) (ε : A → Bool) :
    randomSign (flipSignEquiv i ε) i= -randomSign ε i := by
  cases hi : ε i <;> norm_num [randomSign,flipSignEquiv,flipSignAt,hi]

theorem randomSign_flip_other {A : Type*} [DecidableEq A] (i j : A)
    (hji : j≠i) (ε : A → Bool) :
    randomSign (flipSignEquiv i ε) j=randomSign ε j := by
  simp [randomSign,flipSignEquiv,flipSignAt,hji]

theorem randomSign_sum {A : Type*} [Fintype A] [DecidableEq A] (i : A) :
    (∑ ε : A → Bool,randomSign ε i)=0 := by
  have hh := Equiv.sum_comp (flipSignEquiv i) (fun ε => randomSign ε i)
  simp_rw [randomSign_flip_self] at hh
  rw [Finset.sum_neg_distrib] at hh
  linarith

theorem randomSign_pair_sum_zero {A : Type*} [Fintype A] [DecidableEq A]
    (i j : A) (hij : i≠j) : (∑ ε : A → Bool,randomSign ε i*randomSign ε j)=0 := by
  have hh := Equiv.sum_comp (flipSignEquiv i) (fun ε => randomSign ε i*randomSign ε j)
  simp_rw [randomSign_flip_self,randomSign_flip_other i j (Ne.symm hij),neg_mul] at hh
  rw [Finset.sum_neg_distrib] at hh
  linarith

theorem randomSign_pair_sum {A : Type*} [Fintype A] [DecidableEq A] (i j : A) :
    (∑ ε : A → Bool,randomSign ε i*randomSign ε j)=
      if i=j then (Fintype.card (A → Bool):ℝ) else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    simp only [randomSign_mul_self,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  · rw [if_neg hij]
    exact randomSign_pair_sum_zero i j hij

end EntropyDesigns.ExchangeableHierarchy
