/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.TrapRationalData
@[expose] public section
namespace EntropyDesigns
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
theorem fiveTrap_rational_dual : ∀ x : Fin 5 → Bool,(fiveTrapRationalWeights x≠0 → (∑ r : SmallTrapMomentIndex 5,fiveTrapRationalDual r*rationalTrapMomentMatrix 5 r x)=fiveTrapRationalWeights x) ∧ (fiveTrapRationalWeights x=0 → 0<(∑ r : SmallTrapMomentIndex 5,fiveTrapRationalDual r*rationalTrapMomentMatrix 5 r x)) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool]
  repeat' apply And.intro
  all_goals decide +kernel
end EntropyDesigns
