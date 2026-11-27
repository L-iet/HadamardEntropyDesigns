module

public import EntropyDesigns.BinaryHyperplanes

/-! # Explicit probability laws in every missing additive direction -/

@[expose] public section
namespace EntropyDesigns

theorem missing_direction_nonempty {d : ℕ} (B : Finset (Finset (Fin d)))
    (c : Finset (Fin d)) (hmissing : c ∉ maskSumset (insert ∅ B)) : c.Nonempty := by
  classical
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hc
  apply hmissing
  rw [hc]
  exact (mem_maskSumset _ _).mpr ⟨∅, by simp, ∅, by simp, by simp⟩

theorem missing_direction_laws {d : ℕ} (B : Finset (Finset (Fin d))) (hB : ∅ ∉ B)
    (c : Finset (Fin d)) (hmissing : c ∉ maskSumset (insert ∅ B))
    (t : ℝ) (ht : -1 ≤ t) (ht' : t ≤ 1) :
    (∀ x, 0 ≤ characterTilt c t x) ∧ (∑ x, characterTilt c t x = 1) ∧
      (∀ S ∈ B, walshCoefficient (characterTilt c t) S = 0) ∧
      (∀ S ∈ B, ∀ T ∈ B, S ≠ T →
        ∑ x, characterTilt c t x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) ∧
      collision (characterTilt c t) = (1 + t ^ 2) / (2 : ℝ) ^ d := by
  classical
  have hc := missing_direction_nonempty B c hmissing
  have hzero : ∀ S ∈ maskSumset (insert ∅ B), S ≠ ∅ →
      walshCoefficient (characterTilt c t) S = 0 := by
    intro S hS hnonempty
    have hSc : S ≠ c := by
      intro h
      exact hmissing (h ▸ hS)
    rw [characterTilt_coefficient c hc]
    simp [hnonempty, hSc]
  have hmoments := (observed_moments_iff_mask_cover B hB _).mpr hzero
  exact ⟨characterTilt_nonneg c t ht ht', characterTilt_mass c hc t,
    hmoments.1, hmoments.2, characterTilt_collision c hc t⟩

end EntropyDesigns
