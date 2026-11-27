/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof73
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
theorem rational_trap_moment_xor (s t : Fin 4 → Bool) (r : SmallTrapMomentIndex 4) :
    rationalTrapMomentMatrix 4 r (fun i => xor (t i) (s i))=
      rationalTrapMomentMatrix 4 r s*rationalTrapMomentMatrix 4 r t := by
  have hb (a b : Bool) : (bitSign (xor a b):ℚ)=(bitSign a:ℚ)*(bitSign b:ℚ) := by
    cases a <;> cases b <;> norm_num [bitSign]
  rcases r with r|r
  · cases r
    simp [rationalTrapMomentMatrix]
  · rcases r with i|ij
    · simp only [rationalTrapMomentMatrix,Sum.elim_inr,Sum.elim_inl,hb]
      ring
    · simp only [rationalTrapMomentMatrix,Sum.elim_inr,Sum.elim_inl,hb]
      ring

theorem four_gradient_interpolation_certificate : ∀ (s x t : Fin 4 → Bool),
    fourTranslatedWeights s x≠0 → fourTranslatedWeights s t≠0 →
    (∑ r, fourTranslatedInterpolation s x r*rationalTrapMomentMatrix 4 r t)=if t=x then 1 else 0 := by
  intro s x t hx ht
  have hinj : Function.Injective (fun v : Fin 4 → Bool => fun i => xor (v i) (s i)) := by
    intro u v huv
    funext i
    have he := congrFun huv i
    cases hu : u i <;> cases hv : v i <;> cases hs : s i <;> simp [hu,hv,hs] at he ⊢
  have heq : (fun i => xor (t i) (s i))=(fun i => xor (x i) (s i)) ↔ t=x := hinj.eq_iff
  have hbase := fourTrap_rational_interpolation (fun i => xor (x i) (s i))
    (fun i => xor (t i) (s i)) hx ht
  simp only [heq] at hbase
  simpa only [fourTranslatedInterpolation,rational_trap_moment_xor,mul_assoc] using hbase

end
end EntropyDesigns
