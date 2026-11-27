/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof90
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
theorem four_uniform_power_gradient_strict (i : Fin 5) (b : Bool) {r : ℝ} (hr : 1<r) :
    ∀ z∈momentTangentCone (cubeProbabilityMomentMatrix 4) (fourUniformLaw i b), z≠0 →
      lawOverlap (fun x => (fourUniformLaw i b x)^(r-1)) z<0 := by
  let c : ℝ := (1/8:ℝ)^(r-1)
  have hc : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  have hValue (x : Fin 4 → Bool) :
      dualMomentValues (cubeProbabilityMomentMatrix 4) (fourGradientDual (fun _ => false) c c) x=c := by
    rw [four_gradient_dual_value]; simp
  apply gradient_dual_interpolation_strict_tangent (cubeProbabilityMomentMatrix 4)
    (fourUniformLaw i b) (fun x => (fourUniformLaw i b x)^(r-1))
    (fourGradientDual (fun _ => false) c c) (fun x r => (fourUniformInterpolation i x r : ℝ))
  · intro x hx; rw [hx,Real.zero_rpow (sub_pos.mpr hr).ne']
  · intro x hx
    rw [hValue]
    rcases (four_uniform_weight_profile_certificate i b).1 x with h0|h8
    · have h0R : fourUniformLaw i b x=0 := by unfold fourUniformLaw; rw [h0]; norm_num
      exact False.elim (hx h0R)
    · unfold fourUniformLaw
      rw [h8]
      norm_num
      rfl
  · intro x _; rw [hValue]; exact hc
  · intro x hx t ht; exact four_uniform_interpolation_real i b x t hx ht


end
end EntropyDesigns
