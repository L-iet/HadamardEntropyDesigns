/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Exact balanced sign frames; transport to quadratic restriction codes is separate. -/
module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Int.Basic
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped BigOperators

def balancedWitnessWord (i : Fin 7) : ℕ :=
  match i.val with
  | 0 => 246
  | 1 => 826
  | 2 => 1372
  | 3 => 1708
  | 4 => 3178
  | 5 => 3504
  | _ => 3606

def balancedWitnessSign (i : Fin 7) (j : Fin 12) : ℤ :=
  if (balancedWitnessWord i).testBit j.val then -1 else 1

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

theorem balancedWitness_entries :
    ∀ i j,balancedWitnessSign i j=1 ∨ balancedWitnessSign i j= -1 := by decide

theorem balancedWitness_balance :
    ∀ i : Fin 7,(∑ j : Fin 12,balancedWitnessSign i j)=0 := by decide

theorem balancedWitness_orthogonal :
    ∀ i k : Fin 7,i≠k →
      (∑ j : Fin 12,balancedWitnessSign i j*balancedWitnessSign k j)=0 := by decide

theorem balancedWitness_gram_diagonal :
    ∀ i : Fin 7,(∑ j : Fin 12,balancedWitnessSign i j*balancedWitnessSign i j)=12 := by decide

end EntropyDesigns.QuadraticRefinement
