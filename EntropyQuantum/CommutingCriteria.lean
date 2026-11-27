/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.RankOneAlgebra
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem commuting_distinct_normalized (o : ι) (a b : ℝ) (ha : a≠0) (hb : b≠0)
    (v w : ι → ℝ) (hv : v o=1) (hw : w o=1) (hdist : v≠w)
    (hc : effect a v*effect b w=effect b w*effect a v) : inner v w=0 := by
  by_contra hinner
  apply hdist
  have hzero : commutator (effect a v) (effect b w)=0 := sub_eq_zero.mpr hc
  rw [effect_commutator] at hzero
  funext j
  have hj := congrArg (fun M : Matrix ι ι ℝ => M o j) hzero
  have hj' : (a*b*inner v w)*(w j-v j)=0 := by
    simpa [Matrix.smul_apply,Matrix.sub_apply,outer,hv,hw] using hj
  have hdiff : w j-v j=0 := (mul_eq_zero.mp hj').resolve_left (mul_ne_zero (mul_ne_zero ha hb) hinner)
  linarith

theorem orthogonal_effects_commute (a b : ℝ) (v w : ι → ℝ) (h : inner v w=0) :
    effect a v*effect b w=effect b w*effect a v := by
  apply sub_eq_zero.mp
  change commutator (effect a v) (effect b w)=0
  rw [effect_commutator,h]
  simp

theorem normalized_commute_iff (o : ι) (a b : ℝ) (ha : a≠0) (hb : b≠0)
    (v w : ι → ℝ) (hv : v o=1) (hw : w o=1) (hdist : v≠w) :
    effect a v*effect b w=effect b w*effect a v ↔ inner v w=0 :=
  ⟨commuting_distinct_normalized o a b ha hb v w hv hw hdist,
    orthogonal_effects_commute a b v w⟩
end
end EntropyDesigns.Quantum
