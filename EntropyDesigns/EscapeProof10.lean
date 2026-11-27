/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof09
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
theorem four_bit_escape_exposed_edge (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    IsExposed ℝ {q : (Fin 4 → Bool) → ℝ | cubeProbabilityFeasible q}
      (segment ℝ (fourTranslatedLaw s) (fourUniformLaw i b)) ∧
    fourTranslatedLaw s≠fourUniformLaw i b := by
  classical
  let J := {j : Fin 5 // j≠i}
  let L : J → StrongDual ℝ ((Fin 4 → Bool) → ℝ) := fun j =>
    (2*(fourHighCharacter j.val s : ℝ)) • fourWalshCoefficientLinear j.val -
      ∑ k : Fin 5, (fourHighCharacter k s : ℝ) • fourWalshCoefficientLinear k
  have hEval (j : J) (q : (Fin 4 → Bool) → ℝ) : L j q=
      2*(fourHighCharacter j.val s : ℝ)*fourWalshCoefficients q j.val-
        (∑ k, (fourHighCharacter k s : ℝ)*fourWalshCoefficients q k) := by
    simp [L,four_walsh_coefficient_linear_apply]
  have hs (j : Fin 5) : (fourHighCharacter j s : ℝ)=1 ∨ (fourHighCharacter j s : ℝ)= -1 := by
    rcases (four_translated_certificate s).2.2.2.2.2 j with h|h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hProd : (∏ j : Fin 5, (fourHighCharacter j s : ℝ))=1 := by
    exact_mod_cast four_high_character_certificate.2.2.2.2.1 s
  have hPos (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) (j : J) :
      0 ≤ (1:ℝ)+L j q := by
    rw [hEval]
    have h := four_parameter_slack_nonnegative (fun k => (fourHighCharacter k s : ℝ)) hs hProd
      (fourWalshCoefficients q) (four_coefficients_feasible q hq) j.val
    linarith
  have hEx := nonnegative_slack_face_exposed {q : (Fin 4 → Bool) → ℝ | cubeProbabilityFeasible q}
    L (fun _ => 1) hPos
  have hSet : {q : (Fin 4 → Bool) → ℝ | cubeProbabilityFeasible q ∧ ∀ j : J, 1+L j q=0}=
      segment ℝ (fourTranslatedLaw s) (fourUniformLaw i b) := by
    ext q
    constructor
    · rintro ⟨hq,hFace⟩
      have hF (j : Fin 5) (hj : j≠i) :
          1+2*(fourHighCharacter j s : ℝ)*fourWalshCoefficients q j-
            (∑ k, (fourHighCharacter k s : ℝ)*fourWalshCoefficients q k)=0 := by
        have h := hFace ⟨j,hj⟩
        rw [hEval] at h
        linarith
      obtain ⟨t,ht0,ht1,hqEq⟩ := four_translated_edge_face s i b hb q hq hF
      rw [segment_eq_image]
      refine ⟨t,⟨ht0,ht1⟩,?_⟩
      ext x
      exact (congrFun hqEq x).symm
    · rw [segment_eq_image]
      rintro ⟨t,ht,rfl⟩
      refine ⟨cube_probability_feasible_segment (four_translated_feasible s)
        (four_uniform_feasible i b) ht.1 ht.2,?_⟩
      intro j
      rw [hEval]
      have h := four_segment_common_slacks s i b hb t j.val j.property
      change 1+(2*(fourHighCharacter j.val s : ℝ)*
        fourWalshCoefficients (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x) j.val-
        (∑ k, (fourHighCharacter k s : ℝ)*
          fourWalshCoefficients (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x) k))=0
      linarith
  refine ⟨?_,?_⟩
  · rw [← hSet]
    exact hEx
  · intro hEq
    have hC := congrArg collision hEq
    rw [four_translated_collision,four_uniform_collision] at hC
    norm_num at hC



end EntropyDesigns
