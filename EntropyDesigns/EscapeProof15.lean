/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof14
public import EntropyDesigns.FourBitSharpBarrier
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
set_option Elab.async false
@[expose] public section
set_option maxHeartbeats 4000000
namespace EntropyDesigns
open Set
theorem four_bit_exact_escape_rule (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → cubeProbabilityFeasible
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)) ∧
    (∀ t : ℝ, collision (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)=
      7/72-t/36+t^2/18) ∧
    collision (fourUniformLaw i b)-collision (fourTranslatedLaw s)=(1/36:ℝ) ∧
    (∀ t : ℝ, 0<t → t<1/2 → collision
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)<collision (fourTranslatedLaw s)) ∧
    collision (fun x => (1-(1/2:ℝ))*fourTranslatedLaw s x+(1/2:ℝ)*fourUniformLaw i b x)=7/72 ∧
    (∀ t : ℝ, (3/32:ℝ) ≤ collision
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)) ∧
    collision (fun x => (1-(1/4:ℝ))*fourTranslatedLaw s x+(1/4:ℝ)*fourUniformLaw i b x)=3/32 := by
  have h := four_bit_aligned_escape s i b hb
  refine ⟨h.2.2.1,?_,h.2.2.2.2.1,?_,?_,?_,?_⟩
  · intro t; rw [h.2.2.2.1]; ring
  · intro t ht ht'
    rw [h.2.2.2.1,four_translated_collision]
    nlinarith [mul_pos ht (by linarith : 0<(1/2:ℝ)-t)]
  · rw [h.2.2.2.1]; norm_num
  · intro t; rw [h.2.2.2.1]; nlinarith [sq_nonneg (t-1/4)]
  · rw [h.2.2.2.1]; norm_num


end EntropyDesigns
