/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySpanningSlopes.SpanningDistance
public import EntropySpanningSlopes.SpanningData
public import EntropySpanningSlopes.KnownOrderOptimizer
public import EntropyConcentration.StrictBarrier
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open SupportFace ConcentratedFamily

theorem spanning_plane_full_properties {k s : ℕ} (hk : 2≤k) (hkh : k<2^s) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    let p := uniformFiniteLaw (planeSupport hs e i0 t)
    sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
      (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
      (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
        ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
          ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
        (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
        collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
      (∀ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
          1-1/(k:ℝ)≤totalVariation p q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation p q=1-1/(k:ℝ)) := by
  classical
  let p := uniformFiniteLaw (planeSupport hs e i0 t)
  have hs2 := (spanning_seed_dimension hk hkh).1
  have hp : sourceFeasible i0 p := plane_uniform_feasible hk hs e he i0 t ht
  have hsupport : sourceSupported e i0 p := plane_uniform_source_supported hs e i0 t
  have hcard := planeSupport_card hk hs e i0 t ht
  have hCp : collision p=1/((2:ℝ)^s)^2 := plane_uniform_collision hk hs e i0 t ht
  have hstrict := Concentration.face_optimum_strict_local_collision hk e i0 p hp hsupport hCp
  obtain ⟨q,hq,hCq,hglobal⟩ := source_optimizer_of_known_hadamard i0 e K hK
  have hratio : collision p/collision q=(k:ℝ)/(2:ℝ)^s := by
    rw [hCp,hCq]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    have hkR : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt i0.isLt))
    have hh : (2:ℝ)^s≠0 := pow_ne_zero s (by norm_num)
    field_simp <;> ring
  have hd := spanning_plane_sharp_distance_of_hadamard hk hs hs2 e he i0 t ht hzero R hspan hcomp hsmall K hK
  exact ⟨hp,hsupport,hcard,hCp,hstrict,⟨q,hq,hCq,hglobal,hratio⟩,hd.1,hd.2⟩

end
end EntropyDesigns.SpanningSlopes
