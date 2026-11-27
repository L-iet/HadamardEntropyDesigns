/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.FamilyInputs
public import EntropyConcentratedFamily.PlaneLaw
public import EntropyConcentratedFamily.GlobalOptimizer
public import EntropyConcentration.StrictBarrier
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.ConcentratedFamily
noncomputable section
open SupportFace

theorem concentrated_witness_exists {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ hs : s≠0,∃ t : Fin k → GaloisField 2 s,Function.Injective t ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
      sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
      (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
      (∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → sourceSupported e i0 q → collision q≤collision p) ∧
      (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
        ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
          ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
        (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
        collision p/collision q=(k:ℝ)/(2:ℝ)^s) := by
  classical
  let hs : s≠0 := (family_parameters hk hsize).2.1
  obtain ⟨t,ht⟩ := concentrated_slopes_exist hk hsize
  let p := uniformFiniteLaw (planeSupport hs e i0 t)
  have hp : sourceFeasible i0 p := plane_uniform_feasible hk hs e he i0 t ht
  have hsupport : sourceSupported e i0 p := plane_uniform_source_supported hs e i0 t
  have hcard := planeSupport_card hk hs e i0 t ht
  have hCp : collision p=1/((2:ℝ)^s)^2 := plane_uniform_collision hk hs e i0 t ht
  have hface : ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → sourceSupported e i0 q →
      collision q≤collision p := by
    intro q hq hqsupport
    rw [hCp]
    exact (source_collision_upper hk e i0 q hq hqsupport).2
  have hstrict := EntropyDesigns.Concentration.face_optimum_strict_local_collision
    hk e i0 p hp hsupport hCp
  obtain ⟨q,hq,hCq,hglobal⟩ := source_global_optimizer r hkpow i0
  have hratio : collision p/collision q=(k:ℝ)/(2:ℝ)^s := by
    rw [hCp,hCq]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    have hkR : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i0.isLt))
    have hh : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
    field_simp <;> ring
  exact ⟨hs,t,ht,hp,hsupport,hcard,hCp,hface,hstrict,⟨q,hq,hCq,hglobal,hratio⟩⟩

end
end EntropyDesigns.ConcentratedFamily
