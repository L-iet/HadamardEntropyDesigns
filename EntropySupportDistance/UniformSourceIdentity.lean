/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SourceDistanceLower
public import EntropyDesigns.WalshSubset
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section

theorem supported_uniform_source_identity {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hsupport : sourceSupported e i0 p)
    (hweight : ∀ x : BlockSeeds k s,p (sourceCode e i0 x)=1/((2:ℝ)^s)^k) :
    p=uniformFiniteLaw (observedSupport e i0) := by
  classical
  have hcard : (observedSupport e i0).card=(2^s)^k := by
    rw [observedSupport,Finset.card_image_of_injective _ (sourceCode_injective e i0)]
    simp [BlockSeeds]
  funext y
  by_cases hy : y∈observedSupport e i0
  · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
    rw [hweight]
    simp only [uniformFiniteLaw,hy,ite_true,hcard,Nat.cast_pow,Nat.cast_ofNat]
  · have hp : p y=0 := by
      apply hsupport y
      rintro ⟨x,hx⟩
      exact hy (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩)
    simp [uniformFiniteLaw,hy,hp]

theorem uniform_observed_source_feasible {k s : ℕ} (hk : 2≤k) (hkh : k≤2^s)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    sourceFeasible i0 (uniformFiniteLaw (observedSupport e i0)) := by
  obtain ⟨p,hp,hsupport,_,hweight,_⟩ := source_uniform_law hk hkh e he i0
  rw [←supported_uniform_source_identity e i0 p hsupport hweight]
  exact hp

end
end EntropyDesigns.SupportFace
