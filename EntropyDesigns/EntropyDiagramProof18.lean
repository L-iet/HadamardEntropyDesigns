/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof17
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
theorem four_real_parity_signs_code (s : Fin 5 → ℝ)
    (hs : ∀ j, s j=1 ∨ s j= -1) (hp : (∏ j, s j)=1) :
    ∃ u : Fin 4 → Bool, ∀ j, (fourHighCharacter j u : ℝ)=s j := by
  classical
  let vb : Fin 5 → Bool := fun j => if s j=1 then false else true
  have hV (j : Fin 5) : (bitSign (vb j) : ℝ)=s j := by
    rcases hs j with h|h <;> norm_num [vb,h,bitSign]
  have hProd : (∏ j, bitSign (vb j))=(1:ℤ) := by
    have hReal : (∏ j, (bitSign (vb j) : ℝ))=1 := by simpa only [hV] using hp
    exact_mod_cast hReal
  obtain ⟨u,hu⟩ := four_high_character_certificate.2.2.2.2.2 vb hProd
  refine ⟨u,?_⟩
  intro j
  rw [hu]
  exact hV j


end
end EntropyDesigns
