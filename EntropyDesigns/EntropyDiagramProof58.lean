/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof57
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
theorem four_order_reversing_objective_minimizers
    (f g : ((Fin 4 → Bool) → ℝ) → ℝ)
    (hf : StrictConvexOn ℝ {p : (Fin 4 → Bool) → ℝ | ∀ x, 0 ≤ p x} f)
    (U W A B : ℝ) (hU : ∀ i b, f (fourUniformLaw i b)=U)
    (hW : ∀ s, f (fourTranslatedLaw s)=W)
    (hA : ∀ i b, g (fourUniformLaw i b)=A)
    (hB : ∀ s, g (fourTranslatedLaw s)=B)
    (hOrder : ∀ p q, cubeProbabilityFeasible p → cubeProbabilityFeasible q →
      (g p ≤ g q ↔ f q ≤ f p))
    (q : (Fin 4 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) :
    (∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → g q ≤ g v) ↔
      (∃ (i : Fin 5) (b : Bool), q=fourUniformLaw i b ∧ A ≤ B) ∨
      (∃ s : Fin 4 → Bool, q=fourTranslatedLaw s ∧ B ≤ A) := by
  have hOpt : (∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → g q ≤ g v) ↔
      (∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → f v ≤ f q) := by
    constructor
    · intro h v hv; exact (hOrder q v hq hv).mp (h v hv)
    · intro h v hv; exact (hOrder q v hq hv).mpr (h v hv)
  have hAB : (A ≤ B) ↔ W ≤ U := by
    have h := hOrder (fourUniformLaw 0 false) (fourTranslatedLaw (fun _ => false))
      (four_uniform_feasible 0 false) (four_translated_feasible _)
    simpa only [hA,hB,hU,hW] using h
  have hBA : (B ≤ A) ↔ U ≤ W := by
    have h := hOrder (fourTranslatedLaw (fun _ => false)) (fourUniformLaw 0 false)
      (four_translated_feasible _) (four_uniform_feasible 0 false)
    simpa only [hA,hB,hU,hW] using h
  rw [hOpt,four_objective_global_maximizers f hf U W hU hW q hq]
  simp only [hAB,hBA]

end
end EntropyDesigns
