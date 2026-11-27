/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof00
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
theorem four_parameter_sign_symmetry (a s : Fin 5 → ℝ)
    (ha : fourWalshParameterFeasible a) (hs : ∀ j, s j=1 ∨ s j= -1)
    (hp : (∏ j, s j)=1) : fourWalshParameterFeasible (fun j => s j*a j) := by
  intro v hv hProd
  have hSigns (j : Fin 5) : v j*s j=1 ∨ v j*s j= -1 := by
    rcases hv j with h|h <;> rcases hs j with h'|h' <;> rw [h,h'] <;> norm_num
  have hP : (∏ j, v j*s j)=1 := by rw [Finset.prod_mul_distrib,hp,hProd]; norm_num
  have h := ha (fun j => v j*s j) hSigns hP
  simpa only [mul_assoc] using h


end EntropyDesigns
