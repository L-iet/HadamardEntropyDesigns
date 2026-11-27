/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof31
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
theorem four_objective_global_maximizers (f : ((Fin 4 → Bool) → ℝ) → ℝ)
    (hf : StrictConvexOn ℝ {p : (Fin 4 → Bool) → ℝ | ∀ x, 0 ≤ p x} f)
    (U W : ℝ) (hU : ∀ i b, f (fourUniformLaw i b)=U)
    (hW : ∀ s, f (fourTranslatedLaw s)=W)
    (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) :
    (∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → f v ≤ f q) ↔
      (∃ (i : Fin 5) (b : Bool), q=fourUniformLaw i b ∧ W ≤ U) ∨
      (∃ s : Fin 4 → Bool, q=fourTranslatedLaw s ∧ U ≤ W) := by
  constructor
  · intro hMax
    let a := fourWalshCoefficients q
    have ha : a∈convexHull ℝ fourParameterVertexSet :=
      four_parameter_mem_vertex_hull a (four_coefficients_feasible q hq)
    have hStrict : StrictConvexOn ℝ (convexHull ℝ fourParameterVertexSet)
        (fun a => f (fourParameterLaw a)) := by
      rw [four_parameter_polytope_hull]
      exact four_objective_strict_convex f hf
    have hMaxA (v : Fin 5 → ℝ) (hv : v∈convexHull ℝ fourParameterVertexSet) :
        f (fourParameterLaw v) ≤ f (fourParameterLaw a) := by
      rw [four_parameter_polytope_hull] at hv
      have h := hMax (fourParameterLaw v) (four_parameter_law_feasible v hv)
      rwa [four_parameter_law_reconstruct q hq]
    have hVertex := strict_convex_hull_maximizer_in_generators fourParameterVertexSet
      (fun a => f (fourParameterLaw a)) hStrict a ha hMaxA
    have hqEq : fourParameterLaw a=q := four_parameter_law_reconstruct q hq
    rcases hVertex with ⟨i,b,hi⟩|⟨s,hs,hProd,hsEq⟩
    · have hModel : q=fourUniformLaw i b := by
        rw [hi,four_axis_vertex_law] at hqEq; exact hqEq.symm
      left; refine ⟨i,b,hModel,?_⟩
      have h := hMax (fourTranslatedLaw (fun _ => false)) (four_translated_feasible _)
      rwa [hModel,hU,hW] at h
    · obtain ⟨u,hu⟩ := four_weighted_vertex_law s hs hProd
      have hModel : q=fourTranslatedLaw u := by
        rw [hsEq,hu] at hqEq; exact hqEq.symm
      right; refine ⟨u,hModel,?_⟩
      have h := hMax (fourUniformLaw 0 false) (four_uniform_feasible 0 false)
      rwa [hModel,hU,hW] at h
  · rintro (⟨i,b,rfl,hLe⟩|⟨s,rfl,hLe⟩) v hv
    · have h := four_objective_upper_bound f hf U W hU hW v hv
      rw [max_eq_left hLe] at h
      simpa only [hU] using h
    · have h := four_objective_upper_bound f hf U W hU hW v hv
      rw [max_eq_right hLe] at h
      simpa only [hW] using h



end
end EntropyDesigns
