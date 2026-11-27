module

public import EntropyDesigns.MaskCoverage
public import Mathlib.Algebra.BigOperators.Field

/-! # Probability laws in a missing Walsh direction -/

@[expose] public section
namespace EntropyDesigns

noncomputable def characterTilt {d : ℕ} (c : Finset (Fin d)) (t : ℝ)
    (x : Fin d → Bool) : ℝ := (1 + t * (walshChar c x : ℝ)) / (2 : ℝ) ^ d

theorem walshChar_real_total {d : ℕ} (S : Finset (Fin d)) :
    (∑ x : Fin d → Bool, (walshChar S x : ℝ)) =
      if S = ∅ then (2 : ℝ) ^ d else 0 := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp [walshChar]
  · rw [ite_eq_right hS]
    exact walshChar_real_sum_zero S (Finset.nonempty_iff_ne_empty.mpr hS)

theorem characterTilt_coefficient {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty)
    (t : ℝ) (S : Finset (Fin d)) :
    walshCoefficient (characterTilt c t) S = if S = ∅ then 1 else if S = c then t else 0 := by
  classical
  have hformula : walshCoefficient (characterTilt c t) S =
      ((∑ x : Fin d → Bool, (walshChar S x : ℝ)) +
        t * ∑ x : Fin d → Bool, (walshChar c x : ℝ) * (walshChar S x : ℝ)) / (2 : ℝ) ^ d := by
    unfold walshCoefficient
    have hpoint : ∀ x, characterTilt c t x * (walshChar S x : ℝ) =
        ((walshChar S x : ℝ) + t * ((walshChar c x : ℝ) * (walshChar S x : ℝ))) /
          (2 : ℝ) ^ d := by
      intro x
      unfold characterTilt
      ring
    simp_rw [hpoint]
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hformula, walshChar_real_total, walshChar_real_orthogonality]
  have hM : (2 : ℝ) ^ d ≠ 0 := by positivity
  by_cases hS : S = ∅
  · subst S
    simp [hc.ne_empty, hM]
  · by_cases hcS : c = S
    · subst S
      simp [hc.ne_empty, hM]
    · simp [hS, hcS, Ne.symm hcS]

theorem characterTilt_nonneg {d : ℕ} (c : Finset (Fin d)) (t : ℝ)
    (ht : -1 ≤ t) (ht' : t ≤ 1) : ∀ x, 0 ≤ characterTilt c t x := by
  intro x
  apply div_nonneg _ (by positivity)
  rcases walshChar_sign c x with h | h
  · rw [h]
    norm_num
    linarith
  · rw [h]
    norm_num
    linarith

theorem characterTilt_mass {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) (t : ℝ) :
    (∑ x, characterTilt c t x) = 1 := by
  have h := characterTilt_coefficient c hc t ∅
  simpa [walshCoefficient, walshChar] using h

theorem characterTilt_collision {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) (t : ℝ) :
    collision (characterTilt c t) = (1 + t ^ 2) / (2 : ℝ) ^ d := by
  have hsq : ∀ x, (walshChar c x : ℝ) ^ 2 = 1 := by
    intro x
    exact_mod_cast walshChar_sq c x
  have hpoint : ∀ x, characterTilt c t x ^ 2 =
      (1 + t ^ 2 + 2 * t * (walshChar c x : ℝ)) / ((2 : ℝ) ^ d) ^ 2 := by
    intro x
    unfold characterTilt
    rw [div_pow, add_sq, mul_pow, hsq]
    ring
  unfold collision
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum,
    walshChar_real_sum_zero c hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_zero, add_zero]
  field_simp

end EntropyDesigns
