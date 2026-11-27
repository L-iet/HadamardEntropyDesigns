/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof08
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
theorem four_segment_common_slacks (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) (t : ℝ) :
    ∀ j, j≠i →
      1+2*(fourHighCharacter j s : ℝ)*
        fourWalshCoefficients (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x) j-
      (∑ k, (fourHighCharacter k s : ℝ)*
        fourWalshCoefficients (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x) k)=0 := by
  let q : (Fin 4 → Bool) → ℝ := fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x
  have hN (j : Fin 5) : (fourHighCharacter j s : ℝ)*fourWalshCoefficients q j=
      (1-t)/3+t*(if j=i then 1 else 0) := by
    dsimp [q]
    rw [four_walsh_coefficients_segment,four_translated_coefficients,four_uniform_coefficients]
    have hS : (fourHighCharacter j s : ℝ)=1 ∨ (fourHighCharacter j s : ℝ)= -1 := by
      rcases (four_translated_certificate s).2.2.2.2.2 j with h|h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    by_cases hj : j=i
    · subst j
      rw [← hb]
      simp only [ite_true]
      rcases hS with h|h <;> rw [h] <;> ring
    · simp only [if_neg hj]
      rcases hS with h|h <;> rw [h] <;> ring
  have hSum : (∑ k, (fourHighCharacter k s : ℝ)*fourWalshCoefficients q k)=5*((1-t)/3)+t := by
    simp only [hN]
    fin_cases i <;> norm_num [Fin.sum_univ_succ] <;> ring
  intro j hj
  change 1+2*(fourHighCharacter j s : ℝ)*fourWalshCoefficients q j-
    (∑ k, (fourHighCharacter k s : ℝ)*fourWalshCoefficients q k)=0
  rw [mul_assoc,hN,hSum,if_neg hj]
  ring


end EntropyDesigns
