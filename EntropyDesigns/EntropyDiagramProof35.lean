/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof34
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
theorem entropy_transition_strict_convex : StrictConvexOn ℝ Set.univ entropyTransitionPhi := by
  have hD : deriv entropyTransitionPhi=fun x =>
      (4/3:ℝ)^x*Real.log (4/3)+10*((2/3:ℝ)^x*Real.log (2/3)) := by
    funext x; exact (entropy_transition_derivative x).deriv
  apply strictConvexOn_univ_of_deriv2_pos (by unfold entropyTransitionPhi; fun_prop)
  intro x
  change 0<deriv (deriv entropyTransitionPhi) x
  rw [hD]
  have h1 := ((Real.hasStrictDerivAt_const_rpow (by norm_num : (0:ℝ)<4/3) x).hasDerivAt).mul_const (Real.log (4/3))
  have h2 := (((Real.hasStrictDerivAt_const_rpow (by norm_num : (0:ℝ)<2/3) x).hasDerivAt).mul_const (Real.log (2/3))).const_mul 10
  have hD2 : HasDerivAt
      (fun y : ℝ => (4/3:ℝ)^y*Real.log (4/3)+10*((2/3:ℝ)^y*Real.log (2/3)))
      ((4/3:ℝ)^x*Real.log (4/3)*Real.log (4/3)+
        10*((2/3:ℝ)^x*Real.log (2/3)*Real.log (2/3))) x := h1.add h2
  rw [hD2.deriv]
  have hLog : 0<Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  have hPos : 0<(4/3:ℝ)^x*Real.log (4/3)*Real.log (4/3) := by positivity
  have hNonneg : 0<=(10:ℝ)*((2/3:ℝ)^x*Real.log (2/3)*Real.log (2/3)) := by
    have hPow : 0<(2/3:ℝ)^x := Real.rpow_pos_of_pos (by norm_num) x
    have hNN := mul_nonneg hPow.le (sq_nonneg (Real.log (2/3:ℝ)))
    nlinarith only [hNN]
  linarith


end
end EntropyDesigns
