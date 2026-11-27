/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySymmetricCollision.MatchingResults
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Asymptotics.Defs
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open scoped BigOperators

theorem closed_forall_condition {X : Type*} [TopologicalSpace X] {ι : Sort*} {P : X → ι → Prop}
    (h : ∀ i,IsClosed {x | P x i}) : IsClosed {x | ∀ i,P x i} := by
  simpa only [Set.setOf_forall] using isClosed_iInter h

theorem symmetric_laws_compact (d : ℕ) :
    IsCompact {w : (Fin d → Bool) → ℝ | IsSymmetricPairwiseLaw w} := by
  let T : Set (((Fin d → Bool) → ℝ)) := {w | CoordinatePermutationInvariant w ∧
    (∀ i,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
    (∀ i j,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0)}
  have hc : IsClosed T := by
    have hs : IsClosed {w : (Fin d → Bool) → ℝ | CoordinatePermutationInvariant w} := by
      unfold CoordinatePermutationInvariant
      apply closed_forall_condition
      intro σ
      apply closed_forall_condition
      intro x
      exact isClosed_eq (by fun_prop) (by fun_prop)
    have hm : IsClosed {w : (Fin d → Bool) → ℝ | ∀ i,∑ x,w x*(bitSign (x i):ℝ)=0} := by
      apply closed_forall_condition
      intro i
      exact isClosed_eq (by fun_prop) continuous_const
    have hp : IsClosed {w : (Fin d → Bool) → ℝ | ∀ i j,i≠j →
        ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0} := by
      apply closed_forall_condition
      intro i
      apply closed_forall_condition
      intro j
      apply closed_forall_condition
      intro _
      exact isClosed_eq (by fun_prop) continuous_const
    exact hs.inter (hm.inter hp)
  have he : {w : (Fin d → Bool) → ℝ | IsSymmetricPairwiseLaw w}=
      stdSimplex ℝ (Fin d → Bool) ∩ T := by
    ext w
    simp only [Set.mem_setOf_eq,Set.mem_inter_iff,stdSimplex,IsSymmetricPairwiseLaw,T]
    tauto
  rw [he]
  exact (isCompact_stdSimplex ℝ (Fin d → Bool)).inter_right hc

theorem exists_maximum_symmetric_collision (d : ℕ) (hd : 2≤d) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧
      ∀ v : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw v → collision v≤collision w := by
  have hn : Set.Nonempty {w : (Fin d → Bool) → ℝ | IsSymmetricPairwiseLaw w} := by
    obtain ⟨w,hw,_⟩ := exists_matching_symmetric_law d hd
    exact ⟨w,hw⟩
  obtain ⟨w,hw,hmax⟩ := (symmetric_laws_compact d).exists_isMaxOn hn (show ContinuousOn collision _ by
    unfold collision
    fun_prop)
  exact ⟨w,hw,hmax⟩

def maximumSymmetricCollision (d : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧ collision w=c}

theorem maximumSymmetricCollision_spec (d : ℕ) (hd : 2≤d) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧ collision w=maximumSymmetricCollision d ∧
      ∀ v : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw v → collision v≤maximumSymmetricCollision d := by
  obtain ⟨w,hw,hmax⟩ := exists_maximum_symmetric_collision d hd
  have hbound : ∀ c∈{c : ℝ | ∃ v : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw v ∧ collision v=c},c≤collision w := by
    intro c hc
    obtain ⟨v,hv,rfl⟩ := hc
    exact hmax v hv
  have he : maximumSymmetricCollision d=collision w := by
    apply le_antisymm
    · exact csSup_le ⟨collision w,⟨w,hw,rfl⟩⟩ hbound
    · exact le_csSup ⟨collision w,hbound⟩ ⟨w,hw,rfl⟩
  exact ⟨w,hw,he.symm,fun v hv => he.symm ▸ hmax v hv⟩

theorem maximumSymmetricCollision_bounds (d : ℕ) (hd : 7≤d) :
    1/(4*(d:ℝ)^2)≤maximumSymmetricCollision d ∧ maximumSymmetricCollision d<4/(d:ℝ)^2 := by
  obtain ⟨w,hw,he,hmax⟩ := maximumSymmetricCollision_spec d (by omega)
  obtain ⟨v,hv,hlower⟩ := exists_matching_symmetric_law d (by omega)
  refine ⟨hlower.trans (hmax v hv),?_⟩
  rw [←he]
  exact symmetric_collision_rate hd w hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2

theorem maximumSymmetricCollision_theta :
    Asymptotics.IsTheta Filter.atTop maximumSymmetricCollision (fun d : ℕ => 1/(d:ℝ)^2) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound (4:ℝ)
    filter_upwards [Filter.eventually_ge_atTop 7] with d hd
    obtain ⟨hl,hu⟩ := maximumSymmetricCollision_bounds d hd
    have hn : 0≤maximumSymmetricCollision d := (by positivity : (0:ℝ)≤1/(4*(d:ℝ)^2)).trans hl
    rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have he : (4:ℝ)*(1/(d:ℝ)^2)=4/(d:ℝ)^2 := by ring
    rw [he]
    exact hu.le
  · apply Asymptotics.IsBigO.of_bound (4:ℝ)
    filter_upwards [Filter.eventually_ge_atTop 7] with d hd
    obtain ⟨hl,hu⟩ := maximumSymmetricCollision_bounds d hd
    have hn : 0≤maximumSymmetricCollision d := (by positivity : (0:ℝ)≤1/(4*(d:ℝ)^2)).trans hl
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,abs_of_nonneg hn]
    have he : (4:ℝ)*(1/(4*(d:ℝ)^2))=1/(d:ℝ)^2 := by field_simp
    linarith

end
end EntropyDesigns.SymmetricEntropy
