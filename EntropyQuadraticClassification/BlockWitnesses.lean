/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Balanced exact-orthogonality witnesses in both canonical block parity spaces. -/
module
public import EntropyQuadraticClassification.CanonicalBlocks
public import EntropyQuadraticClassification.BalancedWitnesses
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

def independentBalancedWord (i : Fin 7) : ℕ :=
  balancedWitnessWord i/16+(balancedWitnessWord i%16)*256

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem planeWitness_checks : ∀ i : Fin 5,
    SatisfiesChecks (blockChecks planeBlocks)
      (encodedSupport (balancedWitnessWord (Fin.castLE (by decide : 5≤7) i))) := by
  decide +kernel

theorem independentWitness_checks : ∀ i : Fin 7,
    SatisfiesChecks (blockChecks independentBlocks) (encodedSupport (independentBalancedWord i)) := by
  decide +kernel

theorem planeWitness_card : ∀ i : Fin 5,
    (encodedSupport (balancedWitnessWord (Fin.castLE (by decide : 5≤7) i))).card=6 := by
  decide +kernel

theorem independentWitness_card : ∀ i : Fin 7,
    (encodedSupport (independentBalancedWord i)).card=6 := by decide +kernel

theorem independentWitness_intersection : ∀ i j : Fin 7,i≠j →
    (encodedSupport (independentBalancedWord i) ∩ encodedSupport (independentBalancedWord j)).card=3 := by
  decide +kernel

theorem planeWitness_intersection : ∀ i j : Fin 5,i≠j →
    (encodedSupport (balancedWitnessWord (Fin.castLE (by decide : 5≤7) i)) ∩
      encodedSupport (balancedWitnessWord (Fin.castLE (by decide : 5≤7) j))).card=3 := by
  decide +kernel

end EntropyDesigns.QuadraticRefinement
