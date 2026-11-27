/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.CollisionVertex
public import EntropySpanningSlopes.SpanningWitness
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily
open Filter Set
open scoped Topology BigOperators

theorem affine_moment {A : Type*} [Fintype A] (p q f : A → ℝ) (a b : ℝ) :
    (∑ x,(a • p+b • q) x*f x)=a*(∑ x,p x*f x)+b*(∑ x,q x*f x) := by
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,mul_assoc,
    Finset.sum_add_distrib,← Finset.mul_sum]

theorem source_feasible_convex {k s : ℕ} (i0 : Fin k) :
    Convex ℝ {w : SourceOutcome k s i0 → ℝ | sourceFeasible i0 w} := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun x => add_nonneg (mul_nonneg ha (hp.1 x)) (mul_nonneg hb (hq.1 x)),?_,?_,?_⟩
  · change (∑ x,(a*p x+b*q x))=1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,hp.2.1,hq.2.1]
    simpa only [mul_one] using hab
  · intro c
    rw [affine_moment]
    rw [hp.2.2.1 c,hq.2.2.1 c]
    ring
  · intro c d hcd
    simp only [mul_assoc]
    rw [affine_moment]
    have hp' := hp.2.2.2 c d hcd
    have hq' := hq.2.2.2 c d hcd
    simp only [mul_assoc] at hp' hq'
    rw [hp',hq']
    ring

theorem source_strict_local_vertex {k s : ℕ} (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p)
    (ε : ℝ) (hε : 0 < ε)
    (hstrict : ∀ q : SourceOutcome k s i0 → ℝ, sourceFeasible i0 q → q≠p →
      ‖q-p‖<ε → collision q<collision p) :
    p ∈ Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q} := by
  have hlocal : IsLocalMaxOn collision {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q} p := by
    have hball : ∀ᶠ q : SourceOutcome k s i0 → ℝ in 𝓝 p,‖q-p‖<ε := by
      simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds p hε
    filter_upwards [nhdsWithin_le_nhds hball,self_mem_nhdsWithin] with q hclose hq
    by_cases heq : q=p
    · subst q
      exact le_rfl
    · exact (hstrict q hq heq hclose).le
  exact local_collision_max_extreme _ (source_feasible_convex i0) p hp hlocal

theorem plane_uniform_vertex {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    uniformFiniteLaw (planeSupport hs e i0 t) ∈
      Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q} := by
  let p := uniformFiniteLaw (planeSupport hs e i0 t)
  have hp : sourceFeasible i0 p := plane_uniform_feasible hk hs e he i0 t ht
  have hsup : sourceSupported e i0 p := plane_uniform_source_supported hs e i0 t
  have hC : collision p=1/((2:ℝ)^s)^2 := plane_uniform_collision hk hs e i0 t ht
  have hh := Concentration.face_optimum_strict_local_collision hk e i0 p hp hsup hC
  exact source_strict_local_vertex i0 p hp _ hh.1 hh.2

end
end EntropyDesigns.RelativeSequence
