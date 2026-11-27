/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EntropyDiagramProof81
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
theorem differentiable_strict_moment_tangent_local {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : feasibleLaw A b p) (f : (α → ℝ) → ℝ) (L : StrongDual ℝ (α → ℝ))
    (hDeriv : HasFDerivAt f L p)
    (hStrict : ∀ z∈momentTangentCone A p, z≠0 → L z<0) :
    IsLocalMaxOn f {q | feasibleLaw A b q} p ∧
      ∃ ε : ℝ, 0<ε ∧ ∀ q, feasibleLaw A b q → q≠p → ‖q-p‖<ε → f q<f p := by
  classical
  obtain ⟨a,ha,hMargin⟩ := closed_cone_strict_linear_margin (momentTangentCone A p)
    (momentTangentCone_closed A p) (fun z hz t ht => momentTangentCone_smul A p z hz t ht) L hStrict
  obtain ⟨ε,hε,hR⟩ : ∃ ε>0, ∀ q∈Metric.ball p ε,
      ‖f q-f p-L (q-p)‖ ≤ (a/2)*‖q-p‖ :=
    Metric.eventually_nhds_iff_ball.mp (hDeriv.isLittleO.bound (half_pos ha))
  have hDiff (q : α → ℝ) (hq : feasibleLaw A b q) : q-p∈momentTangentCone A p := by
    refine ⟨?_,?_,?_⟩
    · rw [Matrix.mulVec_sub,hq.2.2,hp.2.2,sub_self]
    · simp only [Pi.sub_apply,Finset.sum_sub_distrib,hq.2.1,hp.2.1,sub_self]
    · intro i hi; simpa only [Pi.sub_apply,hi,sub_zero] using hq.1 i
  have hStrictLocal (q : α → ℝ) (hq : feasibleLaw A b q) (hqp : q≠p) (hClose : ‖q-p‖<ε) :
      f q<f p := by
    have hM := hMargin (q-p) (hDiff q hq)
    have hRem := hR q (by simpa only [Metric.mem_ball,dist_eq_norm] using hClose)
    have hNorm : 0<‖q-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
    have hUpper := (le_abs_self (f q-f p-L (q-p))).trans
      (by simpa only [Real.norm_eq_abs] using hRem)
    nlinarith [mul_pos ha hNorm]
  refine ⟨?_,ε,hε,hStrictLocal⟩
  have hBall : ∀ᶠ q : α → ℝ in 𝓝 p, ‖q-p‖<ε := by
    simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds p hε
  have hMem : ∀ᶠ q : α → ℝ in 𝓝[{q | feasibleLaw A b q}] p, feasibleLaw A b q := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds hBall,hMem] with q hClose hq
  by_cases hqp : q=p
  · subst q; exact le_rfl
  · exact (hStrictLocal q hq hqp hClose).le



end
end EntropyDesigns
