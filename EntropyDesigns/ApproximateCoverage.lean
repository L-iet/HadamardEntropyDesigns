module

public import EntropyDesigns.MaskCoverage

/-! # Parseval bounds for approximately isotropic covering masks -/

@[expose] public section
namespace EntropyDesigns
open scoped symmDiff

theorem covered_mask_is_observed {d : ℕ} (B : Finset (Finset (Fin d)))
    (c : Finset (Fin d)) (hc : c ∈ maskSumset (insert ∅ B)) (hne : c ≠ ∅) :
    (∃ S ∈ B, c = S) ∨ ∃ S ∈ B, ∃ T ∈ B, S ≠ T ∧ c = S ∆ T := by
  classical
  obtain ⟨S, hS, T, hT, hsum⟩ := (mem_maskSumset _ c).mp hc
  rcases Finset.mem_insert.mp hS with rfl | hS
  · have hTc : T = c := by simpa [Finset.symmDiff_def] using hsum
    have hTne : T ≠ ∅ := hTc.symm ▸ hne
    exact Or.inl ⟨T, (Finset.mem_insert.mp hT).resolve_left hTne, hTc.symm⟩
  · rcases Finset.mem_insert.mp hT with rfl | hT
    · have hSc : S = c := by simpa [Finset.symmDiff_def] using hsum
      exact Or.inl ⟨S, hS, hSc.symm⟩
    · have hST : S ≠ T := by
        intro h
        subst T
        exact hne (by simpa using hsum.symm)
      exact Or.inr ⟨S, hS, T, hT, hST, hsum.symm⟩

theorem probability_walsh_parseval {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hmass : ∑ x, w x = 1) :
    collision w = (1 + ∑ S ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      walshCoefficient w S ^ 2) / (2 : ℝ) ^ d := by
  classical
  have hzero : walshCoefficient w ∅ = 1 := by simp [walshCoefficient, walshChar, hmass]
  have hpeel := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin d)))
    (fun S => walshCoefficient w S ^ 2) (Finset.mem_univ ∅)
  rw [hzero, one_pow] at hpeel
  have hparse := walsh_parseval w
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ d ≠ 0)).2
  nlinarith

theorem probability_coefficient_bound {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hmass : ∑ x, w x = 1) (ε : ℝ)
    (hcoeff : ∀ S : Finset (Fin d), S ≠ ∅ → |walshCoefficient w S| ≤ ε) :
    collision w ≤ 1 / (2 : ℝ) ^ d + ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d * ε ^ 2 := by
  classical
  let U := (Finset.univ : Finset (Finset (Fin d))).erase ∅
  have hsum : (∑ S ∈ U, walshCoefficient w S ^ 2) ≤ ∑ _S ∈ U, ε ^ 2 := by
    apply Finset.sum_le_sum
    intro S hS
    have h := hcoeff S (Finset.mem_erase.mp hS).1
    have hnonneg : 0 ≤ ε := (abs_nonneg _).trans h
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hnonneg).mpr h
  have hcardN : U.card + 1 = 2 ^ d := by
    have h := Finset.card_erase_add_one (Finset.mem_univ (∅ : Finset (Fin d)))
    simpa [U] using h
  have hcardR : (U.card : ℝ) + 1 = (2 : ℝ) ^ d := by exact_mod_cast hcardN
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hformula := probability_walsh_parseval w hmass
  have hM : (0 : ℝ) < 2 ^ d := by positivity
  have hbound : collision w ≤ (1 + ((2 : ℝ) ^ d - 1) * ε ^ 2) / (2 : ℝ) ^ d := by
    rw [hformula]
    apply div_le_div_of_nonneg_right _ hM.le
    change 1 + (∑ S ∈ U, walshCoefficient w S ^ 2) ≤ _
    have hcard : (U.card : ℝ) = (2 : ℝ) ^ d - 1 := by linarith
    rw [hcard] at hsum
    linarith
  convert hbound using 1
  ring

theorem approximate_mask_cover {d : ℕ} (B : Finset (Finset (Fin d)))
    (hcover : maskSumset (insert ∅ B) = Finset.univ)
    (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) (ε : ℝ)
    (hmean : ∀ S ∈ B, |walshCoefficient w S| ≤ ε)
    (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T →
      |∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ)| ≤ ε) :
    collision w = (1 + ∑ S ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅,
      walshCoefficient w S ^ 2) / (2 : ℝ) ^ d ∧
    collision w ≤ 1 / (2 : ℝ) ^ d + ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d * ε ^ 2 := by
  classical
  refine ⟨probability_walsh_parseval w hmass, probability_coefficient_bound w hmass ε ?_⟩
  intro c hc
  have hmem : c ∈ maskSumset (insert ∅ B) := by rw [hcover]; exact Finset.mem_univ c
  rcases covered_mask_is_observed B c hmem hc with ⟨S, hS, hcS⟩ | ⟨S, hS, T, hT, hST, hcST⟩
  · rw [hcS]
    exact hmean S hS
  · rw [hcST, walshCoefficient_symmDiff]
    exact hpair S hS T hT hST

theorem approximate_cover_error_obstruction {d : ℕ} (B : Finset (Finset (Fin d)))
    (hcover : maskSumset (insert ∅ B) = Finset.univ)
    (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) (ε η : ℝ)
    (hmean : ∀ S ∈ B, |walshCoefficient w S| ≤ ε)
    (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T →
      |∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ)| ≤ ε)
    (N : ℕ) (hN : 0 < N) (hNL : (N : ℝ) < (2 : ℝ) ^ d)
    (hcollision : 1 / (N : ℝ) - η ≤ collision w) :
    ((2 : ℝ) ^ d / (N : ℝ) - 1 - (2 : ℝ) ^ d * η) / ((2 : ℝ) ^ d - 1) ≤ ε ^ 2 := by
  have hupper := (approximate_mask_cover B hcover w hmass ε hmean hpair).2
  have hM : (0 : ℝ) < 2 ^ d := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hM1 : (1 : ℝ) < 2 ^ d := by linarith
  have hupper' : collision w ≤ (1 + ((2 : ℝ) ^ d - 1) * ε ^ 2) / (2 : ℝ) ^ d := by
    convert hupper using 1
    ring
  have hscaled := (le_div_iff₀ hM).mp hupper'
  have hlower := mul_le_mul_of_nonneg_left hcollision hM.le
  have hlower' : (2 : ℝ) ^ d / (N : ℝ) - (2 : ℝ) ^ d * η ≤ (2 : ℝ) ^ d * collision w := by
    convert hlower using 1
    ring
  apply (div_le_iff₀ (sub_pos.mpr hM1)).2
  nlinarith [hlower']

end EntropyDesigns
