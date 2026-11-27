/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.TrapRationalData
@[expose] public section
namespace EntropyDesigns
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
theorem fiveTrap_rational_feasibility : (∀ x,0≤fiveTrapRationalWeights x) ∧ (∑ x,fiveTrapRationalWeights x)=1 ∧ (∀ r,(∑ x,fiveTrapRationalWeights x*rationalTrapMomentMatrix 5 r x)=rationalTrapMomentTarget 5 r) ∧ (∑ x,(fiveTrapRationalWeights x)^2)=7/72 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool]
  repeat' apply And.intro
  all_goals decide +kernel
end EntropyDesigns
