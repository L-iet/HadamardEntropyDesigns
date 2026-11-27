/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof80
public import EntropyDesigns.FourBitEscape
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Slope

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Topology.Order.IntermediateValue
set_option Elab.async false
@[expose] public section
set_option maxHeartbeats 4000000
namespace EntropyDesigns
open Set
noncomputable section

open Filter
open scoped Topology
theorem four_translated_power_gradient_strict (s : Fin 4 → Bool) {r : ℝ} (hr : 1<r) :
    ∀ z∈momentTangentCone (cubeProbabilityMomentMatrix 4) (fourTranslatedLaw s), z≠0 →
      lawOverlap (fun x => (fourTranslatedLaw s x)^(r-1)) z<0 := by
  let u : ℝ := (1/6:ℝ)^(r-1)
  let v : ℝ := (1/12:ℝ)^(r-1)
  have hv : 0<v := Real.rpow_pos_of_pos (by norm_num) _
  have huv : v<u := Real.rpow_lt_rpow (by norm_num) (by norm_num) (sub_pos.mpr hr)
  apply gradient_dual_interpolation_strict_tangent (cubeProbabilityMomentMatrix 4)
    (fourTranslatedLaw s) (fun x => (fourTranslatedLaw s x)^(r-1))
    (fourGradientDual s u v) (fun x r => (fourTranslatedInterpolation s x r : ℝ))
  · intro x hx
    rw [hx,Real.zero_rpow (sub_pos.mpr hr).ne']
  · intro x hx
    rw [four_gradient_dual_value]
    rcases (four_translated_certificate s).1 x with hNonneg
    rcases (four_translated_weight_profile_certificate s).1 x with h0|h6|h12
    · have h0R : fourTranslatedLaw s x=0 := by unfold fourTranslatedLaw; rw [h0]; norm_num
      exact False.elim (hx h0R)
    · simp only [h6,ite_true,one_mul,mul_one]
      unfold fourTranslatedLaw
      rw [h6]
      norm_num
      dsimp [u]
    · simp only [h12]
      unfold fourTranslatedLaw
      rw [h12]
      norm_num
      rfl
  · intro x hx
    have hxQ : fourTranslatedWeights s x=0 := by
      change (fourTranslatedWeights s x : ℝ)=0 at hx
      exact_mod_cast hx
    rw [four_gradient_dual_value,hxQ]
    norm_num
    linarith
  · intro x hx t ht
    exact four_translated_interpolation_real s x t hx ht



end
end EntropyDesigns
