/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof07
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
theorem four_parameter_slack_nonnegative (s : Fin 5 → ℝ)
    (hs : ∀ j, s j=1 ∨ s j= -1) (hProd : (∏ j, s j)=1)
    (a : Fin 5 → ℝ) (ha : fourWalshParameterFeasible a) (j : Fin 5) :
    0 ≤ 1+2*s j*a j-(∑ k, s k*a k) := by
  let v : Fin 5 → ℝ := fun k => (if k=j then 1 else -1)*s k
  have hV (k : Fin 5) : v k=1 ∨ v k= -1 := by
    dsimp [v]
    split_ifs <;> rcases hs k with h|h <;> rw [h] <;> norm_num
  have hP : (∏ k, v k)=1 := by
    dsimp [v]
    rw [Finset.prod_mul_distrib,hProd,mul_one]
    fin_cases j <;> norm_num [Fin.prod_univ_succ]
  have h := ha v hV hP
  have hDot : (∑ k, v k*a k)=2*s j*a j-(∑ k, s k*a k) := by
    calc
      _=∑ k : Fin 5, ((if k=j then 2*s j*a j else 0)-s k*a k) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [v]
        split_ifs with hk
        · subst k; ring
        · ring
      _=_ := by simp [Finset.sum_sub_distrib]
  rw [hDot] at h
  linarith


end EntropyDesigns
