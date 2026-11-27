/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourWalshParameter
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
theorem four_half_coordinate_case_6 (a : Fin 5 → ℝ) (ha : fourWalshParameterFeasible a)
    (hai : a 3 = 1/2) : (∑ j,a j^2)≤1/2 := by
  have h0p := ha (![-1,1,1,-1,1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h0p
  have h0m := ha (![1,-1,-1,-1,-1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h0m
  have sq0 : (-a 0 + a 1 + a 2 + a 4)^2 ≤ 1/4 := by nlinarith only [h0p,h0m]
  have h1p := ha (![1,-1,1,-1,1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h1p
  have h1m := ha (![-1,1,-1,-1,-1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h1m
  have sq1 : (a 0 + -a 1 + a 2 + a 4)^2 ≤ 1/4 := by nlinarith only [h1p,h1m]
  have h2p := ha (![1,1,-1,-1,1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h2p
  have h2m := ha (![-1,-1,1,-1,-1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h2m
  have sq2 : (a 0 + a 1 + -a 2 + a 4)^2 ≤ 1/4 := by nlinarith only [h2p,h2m]
  have h3p := ha (![1,1,1,-1,-1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h3p
  have h3m := ha (![-1,-1,-1,-1,1]) (by intro j; fin_cases j <;> norm_num) (by norm_num [Fin.prod_univ_succ])
  norm_num [Fin.sum_univ_succ, hai] at h3m
  have sq3 : (a 0 + a 1 + a 2 + -a 4)^2 ≤ 1/4 := by nlinarith only [h3p,h3m]
  norm_num [Fin.sum_univ_succ]
  nlinarith only [hai, sq0,sq1,sq2,sq3]
end EntropyDesigns
