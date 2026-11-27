/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourTranslatedData
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
theorem four_uniform_certificate : ∀ (i : Fin 5) (b : Bool),
    (∀ x, 0 ≤ fourUniformWeights i b x) ∧
    (∑ x, fourUniformWeights i b x)=1 ∧
    (∀ r, (∑ x, fourUniformWeights i b x*rationalTrapMomentMatrix 4 r x)=rationalTrapMomentTarget 4 r) ∧
    (∑ x, fourUniformWeights i b x^2)=(1/8 : ℚ) ∧
    (∀ j : Fin 5, (∑ x, fourUniformWeights i b x*(fourHighCharacter j x : ℚ))=
      if j=i then (bitSign b : ℚ) else 0) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool, Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel

end EntropyDesigns
