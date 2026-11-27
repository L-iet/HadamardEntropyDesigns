/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.TrapRationalData
@[expose] public section
namespace EntropyDesigns
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
theorem fourTrap_rational_dual : ∀ x : Fin 4 → Bool,(fourTrapRationalWeights x≠0 → (∑ r : SmallTrapMomentIndex 4,fourTrapRationalDual r*rationalTrapMomentMatrix 4 r x)=fourTrapRationalWeights x) ∧ (fourTrapRationalWeights x=0 → 0<(∑ r : SmallTrapMomentIndex 4,fourTrapRationalDual r*rationalTrapMomentMatrix 4 r x)) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool]
  repeat' apply And.intro
  all_goals decide +kernel
end EntropyDesigns
