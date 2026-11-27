/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof02
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
theorem four_walsh_coefficients_injective (p q : (Fin 4 → Bool) → ℝ)
    (hp : cubeProbabilityFeasible p) (hq : cubeProbabilityFeasible q)
    (hCoeff : ∀ j, fourWalshCoefficients p j=fourWalshCoefficients q j) : p=q := by
  funext x
  have h1 := four_walsh_reconstruction p hp x
  have h2 := four_walsh_reconstruction q hq x
  simp only [hCoeff] at h1
  linarith


end EntropyDesigns
