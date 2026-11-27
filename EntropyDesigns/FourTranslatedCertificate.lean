/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourTranslatedData
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
theorem four_translated_certificate : ∀ s : Fin 4 → Bool,
    (∀ x, 0 ≤ fourTranslatedWeights s x) ∧
    (∑ x, fourTranslatedWeights s x)=1 ∧
    (∀ r, (∑ x, fourTranslatedWeights s x*rationalTrapMomentMatrix 4 r x)=rationalTrapMomentTarget 4 r) ∧
    (∑ x, fourTranslatedWeights s x^2)=(7/72 : ℚ) ∧
    (∀ i : Fin 5, (∑ x, fourTranslatedWeights s x*(fourHighCharacter i x : ℚ))=
      (fourHighCharacter i s : ℚ)/3) ∧
    (∀ i : Fin 5, fourHighCharacter i s=1 ∨ fourHighCharacter i s= -1) := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool]
  repeat' apply And.intro
  all_goals decide +kernel

end EntropyDesigns
