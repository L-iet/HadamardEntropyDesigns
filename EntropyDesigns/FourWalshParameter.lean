/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourWalshFinite
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
def fourWalshParameterFeasible (a : Fin 5 → ℝ) : Prop :=
  ∀ v : Fin 5 → ℝ, (∀ i, v i=1 ∨ v i= -1) → (∏ i, v i)=1 →
    0 ≤ 1+∑ i, v i*a i


end EntropyDesigns
