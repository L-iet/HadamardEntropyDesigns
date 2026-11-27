/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentratedFamily.ConcentratedLimits
@[expose] public section
namespace EntropyDesigns.ModerateSupport
noncomputable section
open SupportFace ConcentratedFamily

def regimeWitness (k s : ℕ) (e : Finset (Fin s)) (i0 : Fin k) : Prop :=
  ∃ hs : s≠0,∃ t : Fin k → GaloisField 2 s,Function.Injective t ∧
    let p := uniformFiniteLaw (planeSupport hs e i0 t)
    sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
    (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/(((2:ℕ):ℝ)^s)^2 ∧
    (0<((2:ℕ):ℝ)/((((2:ℕ):ℝ)^s)^2*((((2:ℕ):ℝ)^s)^2+1)) ∧
      ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
        ‖q-p‖<((2:ℕ):ℝ)/((((2:ℕ):ℝ)^s)^2*((((2:ℕ):ℝ)^s)^2+1)) → collision q<collision p) ∧
    (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
      (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
      collision p/collision q=(k:ℝ)/((2:ℕ):ℝ)^s) ∧
    (∀ q : SourceOutcome k s i0 → ℝ,
      q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
        1-1/(k:ℝ)≤totalVariation p q) ∧
    (∃ q : SourceOutcome k s i0 → ℝ,
      q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
        totalVariation p q=1-1/(k:ℝ))

theorem regime_witness_exists {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    regimeWitness k s e i0 := by
  obtain ⟨hs,t,ht,hp,hsupport,hcard,hC,_hface,hstrict,hglobal⟩ :=
    concentrated_witness_exists hk r hkpow hsize e he i0
  have hd := concentrated_sharp_distance hk r hkpow hsize hs e he i0 t ht
  exact ⟨hs,t,ht,hp,hsupport,hcard,hC,hstrict,hglobal,hd.1,hd.2⟩

end
end EntropyDesigns.ModerateSupport
