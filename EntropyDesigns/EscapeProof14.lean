/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof13
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
theorem four_bit_escape_circuit (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    (cubeProbabilityMomentMatrix 4).mulVec (fourUniformLaw i b-fourTranslatedLaw s)=0 ∧
    (∑ x, (fourUniformLaw i b-fourTranslatedLaw s) x)=0 ∧
    (Finset.univ.filter (fun x => (fourUniformLaw i b-fourTranslatedLaw s) x≠0)).card=12 ∧
    ∀ z : (Fin 4 → Bool) → ℝ,
      (cubeProbabilityMomentMatrix 4).mulVec z=0 → (∑ x, z x)=0 →
      (∀ x, (fourUniformLaw i b-fourTranslatedLaw s) x=0 → z x=0) → z≠0 →
      ∃ r : ℝ, r≠0 ∧ z=r • (fourUniformLaw i b-fourTranslatedLaw s) := by
  have hDir := (four_bit_escape_supported_kernel s i b hb
    (fourUniformLaw i b-fourTranslatedLaw s)).mpr ⟨1,by simp⟩
  refine ⟨hDir.1,hDir.2.1,?_,?_⟩
  · have hCount := (four_bit_aligned_escape s i b hb).2.2.2.2.2
    have hNe (x : Fin 4 → Bool) :
        ((fourUniformLaw i b-fourTranslatedLaw s) x≠0) ↔
        fourTranslatedLaw s x≠fourUniformLaw i b x := by
      simp only [Pi.sub_apply,sub_ne_zero,ne_comm]
    simp_rw [hNe]
    exact hCount
  · intro z hAz hSum hSupport hNe
    have hS (x : Fin 4 → Bool) (hx : fourTranslatedLaw s x=0) (hy : fourUniformLaw i b x=0) : z x=0 := by
      apply hSupport x
      simp only [Pi.sub_apply,hx,hy,sub_self]
    obtain ⟨r,hr⟩ := (four_bit_escape_supported_kernel s i b hb z).mp ⟨hAz,hSum,hS⟩
    refine ⟨r,?_,hr⟩
    intro h0
    rw [h0,zero_smul] at hr
    exact hNe hr


end EntropyDesigns
