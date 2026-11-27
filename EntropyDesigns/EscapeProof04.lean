/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof03
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
theorem four_translated_edge_face (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) (q : (Fin 4 → Bool) → ℝ)
    (hq : cubeProbabilityFeasible q)
    (hFace : ∀ j, j≠i → 1+2*(fourHighCharacter j s : ℝ)*fourWalshCoefficients q j-
      (∑ k, (fourHighCharacter k s : ℝ)*fourWalshCoefficients q k)=0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      q=fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x := by
  have hs (j : Fin 5) : (fourHighCharacter j s : ℝ)=1 ∨ (fourHighCharacter j s : ℝ)= -1 := by
    rcases (four_translated_certificate s).2.2.2.2.2 j with h|h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hProd : (∏ j : Fin 5, (fourHighCharacter j s : ℝ))=1 := by
    exact_mod_cast four_high_character_certificate.2.2.2.2.1 s
  have hP := four_parameter_sign_symmetry (fourWalshCoefficients q)
    (fun j => (fourHighCharacter j s : ℝ)) (four_coefficients_feasible q hq) hs hProd
  have hFace' : ∀ j, j≠i → 1+2*((fourHighCharacter j s : ℝ)*fourWalshCoefficients q j)-
      (∑ k, (fourHighCharacter k s : ℝ)*fourWalshCoefficients q k)=0 := by
    intro j hj; simpa only [mul_assoc] using hFace j hj
  obtain ⟨t,ht0,ht1,hCoeff⟩ := four_normalized_edge_face i _ hP hFace'
  refine ⟨t,ht0,ht1,?_⟩
  apply four_walsh_coefficients_injective q _ hq
    (cube_probability_feasible_segment (four_translated_feasible s) (four_uniform_feasible i b) ht0 ht1)
  intro j
  rw [four_walsh_coefficients_segment,four_translated_coefficients,four_uniform_coefficients]
  have h := hCoeff j
  have hbi : (bitSign b : ℝ)=(fourHighCharacter i s : ℝ) := by rw [hb]
  rw [hbi]
  by_cases hj : j=i
  · subst j
    simp only [ite_true] at h ⊢
    rcases hs i with hS|hS <;> rw [hS] at h ⊢ <;> linarith
  · simp only [if_neg hj] at h ⊢
    rcases hs j with hS|hS <;> rw [hS] at h ⊢ <;> linarith


open Set

end EntropyDesigns
