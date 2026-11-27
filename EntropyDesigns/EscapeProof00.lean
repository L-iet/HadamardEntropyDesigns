/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourBitSharpBarrier
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
set_option Elab.async false
@[expose] public section
set_option maxHeartbeats 4000000
namespace EntropyDesigns
open Set
theorem four_normalized_edge_face (i : Fin 5) (a : Fin 5 → ℝ)
    (ha : fourWalshParameterFeasible a)
    (hFace : ∀ j, j≠i → 1+2*a j-(∑ k, a k)=0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      ∀ j, a j=(1-t)/3+t*(if j=i then 1 else 0) := by
  let c : ℝ := ((∑ k, a k)-1)/2
  have hOther (j : Fin 5) (hj : j≠i) : a j=c := by
    have h := hFace j hj
    dsimp [c]
    linarith
  have hForm (j : Fin 5) : a j=if j=i then a i else c := by
    split_ifs with h
    · rw [h]
    · exact hOther j h
  have hSum : (∑ j, a j)=a i+4*c := by
    calc
      _=(∑ j : Fin 5, if j=i then a i else c) := Finset.sum_congr rfl (fun j _ => hForm j)
      _=a i+4*c := by fin_cases i <;> norm_num [Fin.sum_univ_succ] <;> ring
  have hAi : a i=1-2*c := by dsimp [c] at hSum ⊢; linarith
  have hUpper : c ≤ 1/3 := by
    have h := ha (fun j => if j=i then 1 else -1)
      (fun j => by split_ifs <;> simp)
      (by fin_cases i <;> norm_num [Fin.prod_univ_succ])
    have hDot : (∑ j : Fin 5, (if j=i then (1:ℝ) else -1)*a j)=a i-4*c := by
      calc
        _=(∑ j : Fin 5, (if j=i then (1:ℝ) else -1)*(if j=i then a i else c)) :=
          Finset.sum_congr rfl (fun j _ => by rw [hForm j])
        _=a i-4*c := by fin_cases i <;> norm_num [Fin.sum_univ_succ] <;> ring
    rw [hDot] at h
    linarith
  have hLower : 0 ≤ c := by
    fin_cases i
    · have h := ha (![-1,-1,1,1,1]) (by intro j; fin_cases j <;> norm_num)
        (by norm_num [Fin.prod_univ_succ])
      norm_num [Fin.sum_univ_succ] at h
      change a 0=1-2*c at hAi
      have h1 : a 1=c := hOther 1 (by decide)
      have h2 : a 2=c := hOther 2 (by decide)
      have h3 : a 3=c := hOther 3 (by decide)
      have h4 : a 4=c := hOther 4 (by decide)
      linarith
    · have h := ha (![1,-1,-1,1,1]) (by intro j; fin_cases j <;> norm_num)
        (by norm_num [Fin.prod_univ_succ])
      norm_num [Fin.sum_univ_succ] at h
      change a 1=1-2*c at hAi
      have h0 : a 0=c := hOther 0 (by decide)
      have h2 : a 2=c := hOther 2 (by decide)
      have h3 : a 3=c := hOther 3 (by decide)
      have h4 : a 4=c := hOther 4 (by decide)
      linarith
    · have h := ha (![1,1,-1,-1,1]) (by intro j; fin_cases j <;> norm_num)
        (by norm_num [Fin.prod_univ_succ])
      norm_num [Fin.sum_univ_succ] at h
      change a 2=1-2*c at hAi
      have h0 : a 0=c := hOther 0 (by decide)
      have h1 : a 1=c := hOther 1 (by decide)
      have h3 : a 3=c := hOther 3 (by decide)
      have h4 : a 4=c := hOther 4 (by decide)
      linarith
    · have h := ha (![1,1,1,-1,-1]) (by intro j; fin_cases j <;> norm_num)
        (by norm_num [Fin.prod_univ_succ])
      norm_num [Fin.sum_univ_succ] at h
      change a 3=1-2*c at hAi
      have h0 : a 0=c := hOther 0 (by decide)
      have h1 : a 1=c := hOther 1 (by decide)
      have h2 : a 2=c := hOther 2 (by decide)
      have h4 : a 4=c := hOther 4 (by decide)
      linarith
    · have h := ha (![-1,1,1,1,-1]) (by intro j; fin_cases j <;> norm_num)
        (by norm_num [Fin.prod_univ_succ])
      norm_num [Fin.sum_univ_succ] at h
      change a 4=1-2*c at hAi
      have h0 : a 0=c := hOther 0 (by decide)
      have h1 : a 1=c := hOther 1 (by decide)
      have h2 : a 2=c := hOther 2 (by decide)
      have h3 : a 3=c := hOther 3 (by decide)
      linarith
  refine ⟨1-3*c,by linarith,by linarith,?_⟩
  intro j
  by_cases hj : j=i
  · subst j
    simp only [ite_true]
    linarith
  · rw [hOther j hj,if_neg hj]
    ring



end EntropyDesigns
