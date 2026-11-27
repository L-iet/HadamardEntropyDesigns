/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SharpMixture
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section

theorem uniform_source_sharp_distance {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ p : SourceOutcome k s i0 → ℝ,sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
      collision p=1/((2:ℝ)^s)^k ∧
      (∀ x : BlockSeeds k s,p (sourceCode e i0 x)=1/((2:ℝ)^s)^k) ∧
      (observedSupport e i0).card=(2^s)^k ∧
      (∀ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
          1-1/(k:ℝ)≤totalVariation p q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation p q=1-1/(k:ℝ)) := by
  classical
  have hkh : k≤2^s := by omega
  have hs : 2≤s := by
    by_contra h
    have h01 : s=0 ∨ s=1 := by omega
    rcases h01 with h0|h1
    · subst s;norm_num at hsize;omega
    · subst s;norm_num at hsize;omega
  obtain ⟨K,hK,hfirst,hcol⟩ := normalized_walsh_exists r hkpow i0
  obtain ⟨p,hp,hsupport,hcollision,hweight,hcard⟩ := source_uniform_law hk hkh e he i0
  refine ⟨p,hp,hsupport,hcollision,hweight,hcard,?_,?_⟩
  · intro q hq
    exact source_all_mixtures_distance_lower e i0 hsize p q hp.2.1 hsupport hq
  · exact ⟨completionMixture e i0 K,completionMixture_mem hs e i0 K hK hcol,
      completionMixture_exact_distance hs e i0 K hK hfirst hcol p hp hsupport hweight⟩

end
end EntropyDesigns.SupportFace
