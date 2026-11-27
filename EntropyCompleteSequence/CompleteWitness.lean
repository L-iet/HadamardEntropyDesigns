/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.SourceVertex
public import EntropyCompleteSequence.EntropyExcess
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily SpanningSlopes

def CompleteSpanningWitness (k s : ℕ) (e : Finset (Fin s)) (i0 : Fin k) : Prop :=
  ∃ hs : s≠0,∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
      (sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
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
            totalVariation p q=1-1/(k:ℝ))) ∧
    p ∈ Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q} ∧
    (∃ q : SourceOutcome k s i0 → ℝ, sourceFeasible i0 q ∧
      (∀ α : ℝ, 0<α →
        (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w →
          renyiEntropy q α ≤ renyiEntropy w α) ∧
        renyiEntropy p α - renyiEntropy q α = Real.log ((2:ℝ)^s/(k:ℝ))) ∧
      (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w → minEntropy q ≤ minEntropy w) ∧
      minEntropy p - minEntropy q = Real.log ((2:ℝ)^s/(k:ℝ)))

theorem complete_spanning_witness_exists {k s : ℕ} (hk : 2≤k)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    CompleteSpanningWitness k s e i0 := by
  obtain ⟨hs,R,t,ht,hzero,hRcard,hRzero,hRspan,hRcomp,hfull⟩ :=
    spanning_witness_exists hk hsu hsmall e he i0 K hK
  have hv := plane_uniform_vertex hk hs e he i0 t ht
  have hEnt := plane_entropy_excess hk hs e he i0 t ht K hK
  exact ⟨hs,R,t,ht,hzero,hRcard,hRzero,hRspan,hRcomp,hfull,hv,hEnt⟩

end
end EntropyDesigns.RelativeSequence
