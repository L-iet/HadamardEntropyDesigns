/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourHalfCase0
public import EntropyDesigns.FourHalfCase1
public import EntropyDesigns.FourHalfCase2
public import EntropyDesigns.FourHalfCase3
public import EntropyDesigns.FourHalfCase4
public import EntropyDesigns.FourHalfCase5
public import EntropyDesigns.FourHalfCase6
public import EntropyDesigns.FourHalfCase7
public import EntropyDesigns.FourHalfCase8
public import EntropyDesigns.FourHalfCase9
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
theorem four_walsh_half_coordinate_bound (a : Fin 5 → ℝ)
    (ha : fourWalshParameterFeasible a) (i : Fin 5) (hi : |a i|=1/2) :
    (∑ j, a j^2) ≤ 1/2 := by
  fin_cases i
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp hi with hp|hn
    · exact four_half_coordinate_case_0 a ha hp
    · exact four_half_coordinate_case_1 a ha hn
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp hi with hp|hn
    · exact four_half_coordinate_case_2 a ha hp
    · exact four_half_coordinate_case_3 a ha hn
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp hi with hp|hn
    · exact four_half_coordinate_case_4 a ha hp
    · exact four_half_coordinate_case_5 a ha hn
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp hi with hp|hn
    · exact four_half_coordinate_case_6 a ha hp
    · exact four_half_coordinate_case_7 a ha hn
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1/2)).mp hi with hp|hn
    · exact four_half_coordinate_case_8 a ha hp
    · exact four_half_coordinate_case_9 a ha hn

end EntropyDesigns
