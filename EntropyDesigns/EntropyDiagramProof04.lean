/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof03
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
theorem four_signed_absolute_coordinates (a : Fin 5 → ℝ) :
    ∃ s : Fin 5 → ℝ, (∀ i, s i=1 ∨ s i= -1) ∧
      (∀ i, s i*a i=|a i|) ∧ (∀ i, s i*|a i|=a i) ∧
      ((∏ i, s i)=1 ∨ (∏ i, s i)= -1) := by
  let s : Fin 5 → ℝ := fun i => if 0 ≤ a i then 1 else -1
  have hs (i : Fin 5) : s i=1 ∨ s i= -1 := by dsimp [s]; split_ifs <;> simp
  refine ⟨s,hs,?_,?_,?_⟩
  · intro i
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  · intro i
    dsimp [s]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  · rcases hs 0 with h0|h0 <;> rcases hs 1 with h1|h1 <;>
      rcases hs 2 with h2|h2 <;> rcases hs 3 with h3|h3 <;>
      rcases hs 4 with h4|h4 <;> norm_num [Fin.prod_univ_succ,h0,h1,h2,h3,h4]


end
end EntropyDesigns
