/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourTranslatedData
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
theorem four_aligned_escape_certificate : ∀ (s : Fin 4 → Bool) (i : Fin 5) (b : Bool),
    fourHighCharacter i s=bitSign b →
    (∑ x, fourTranslatedWeights s x*fourUniformWeights i b x)=(1/12 : ℚ) ∧
    (Finset.univ.filter (fun x => fourTranslatedWeights s x≠fourUniformWeights i b x)).card=12 := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, Bool.forall_bool, Fin.forall_fin_succ, Fin.forall_fin_zero]
  repeat' apply And.intro
  all_goals decide +kernel


end EntropyDesigns
