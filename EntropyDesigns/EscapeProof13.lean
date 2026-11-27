/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof12
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
theorem four_bit_escape_supported_kernel (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) (z : (Fin 4 → Bool) → ℝ) :
    ((cubeProbabilityMomentMatrix 4).mulVec z=0 ∧ (∑ x, z x)=0 ∧
      (∀ x, fourTranslatedLaw s x=0 → fourUniformLaw i b x=0 → z x=0)) ↔
    ∃ r : ℝ, z=r • (fourUniformLaw i b-fourTranslatedLaw s) := by
  let A := cubeProbabilityMomentMatrix 4
  let B := cubeProbabilityMomentTarget 4
  have hp : feasibleLaw A B (fourTranslatedLaw s) :=
    (cube_probability_feasible_iff _).mp (four_translated_feasible s)
  have hq : feasibleLaw A B (fourUniformLaw i b) :=
    (cube_probability_feasible_iff _).mp (four_uniform_feasible i b)
  have hEdge : IsExposed ℝ {q | feasibleLaw A B q}
      (segment ℝ (fourTranslatedLaw s) (fourUniformLaw i b)) := by
    have hSet : {q | feasibleLaw A B q}={q : (Fin 4 → Bool) → ℝ | cubeProbabilityFeasible q} := by
      ext q; exact (cube_probability_feasible_iff q).symm
    rw [hSet]
    exact (four_bit_escape_exposed_edge s i b hb).1
  constructor
  · rintro ⟨hAz,hSum,hSupport⟩
    apply exposed_segment_supported_kernel A B (fourTranslatedLaw s) (fourUniformLaw i b)
      hp hq hEdge (1/24) (by norm_num) ?_ z hAz hSum hSupport
    intro x
    rcases four_escape_midpoint_lower_certificate s i b x with h0|hL
    · left
      unfold fourTranslatedLaw fourUniformLaw
      exact_mod_cast h0
    · right
      unfold fourTranslatedLaw fourUniformLaw
      have hh : ((1/24:ℚ):ℝ) ≤ (((fourTranslatedWeights s x+fourUniformWeights i b x)/2:ℚ):ℝ) :=
        Rat.cast_le.mpr hL
      push_cast at hh
      norm_num at hh
      exact hh
  · rintro ⟨r,rfl⟩
    refine ⟨?_,?_,?_⟩
    · rw [Matrix.mulVec_smul,Matrix.mulVec_sub,hp.2.2,hq.2.2,sub_self,smul_zero]
    · simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,← Finset.mul_sum,Finset.sum_sub_distrib,
        hq.2.1,hp.2.1,sub_self,mul_zero]
    · intro x hx hy
      simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,hx,hy,sub_self,mul_zero]


end EntropyDesigns
