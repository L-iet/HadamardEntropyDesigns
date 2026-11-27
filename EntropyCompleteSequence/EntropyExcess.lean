/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.LawEntropy
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily SpanningSlopes

theorem logarithm_entropy_excess (k h : ℝ) (hk : 0 < k) (hh : 0 < h) :
    Real.log (h^2) - Real.log (k*h) = Real.log (h/k) := by
  rw [Real.log_pow, Real.log_mul hk.ne' hh.ne', Real.log_div hh.ne' hk.ne']
  norm_num
  ring

/-- One actual global Hadamard law minimizes every positive-order Renyi
entropy (including Shannon) and min-entropy simultaneously. The plane
law's exact common excess is log(h/k). -/
theorem plane_entropy_excess {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    let p := uniformFiniteLaw (planeSupport hs e i0 t)
    ∃ q : SourceOutcome k s i0 → ℝ, sourceFeasible i0 q ∧
      (∀ α : ℝ, 0<α →
        (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w →
          renyiEntropy q α ≤ renyiEntropy w α) ∧
        renyiEntropy p α - renyiEntropy q α = Real.log ((2:ℝ)^s/(k:ℝ))) ∧
      (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w → minEntropy q ≤ minEntropy w) ∧
      minEntropy p - minEntropy q = Real.log ((2:ℝ)^s/(k:ℝ)) := by
  obtain ⟨q,hq,hqa,hqm⟩ := source_all_entropy_optimizer i0 e K hK
  have hp := plane_all_entropy hk hs e he i0 t ht
  have hkR : (0:ℝ)<k := by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hk
  have hhR : (0:ℝ)<(2:ℝ)^s := pow_pos (by norm_num) s
  have hex : Real.log (((2^s)^2:ℕ):ℝ) - Real.log ((k*2^s:ℕ):ℝ) =
      Real.log ((2:ℝ)^s/(k:ℝ)) := by
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    exact logarithm_entropy_excess (k:ℝ) ((2:ℝ)^s) hkR hhR
  refine ⟨q,hq,?_,?_,?_⟩
  · intro α hα
    refine ⟨?_,?_⟩
    · intro w hw
      rw [hqa α hα]
      exact (source_all_entropy_lower i0 w hw).1 α hα
    · rw [hp.1 α hα, hqa α hα]
      exact hex
  · intro w hw
    rw [hqm]
    exact (source_all_entropy_lower i0 w hw).2
  · rw [hp.2,hqm]
    exact hex

end
end EntropyDesigns.RelativeSequence
