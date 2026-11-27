module

public import EntropyDesigns.ExactExtraction

/-! # Exact finite Fourier-buffer correction -/

@[expose] public section
namespace EntropyDesigns

noncomputable def affineCorrection {α : Type*}
    (w f : α → ℝ) (M B : ℝ) (a : α) : ℝ :=
  (w a + (B - f a) / M) / (1 + B)

theorem affineCorrection_nonneg {α : Type*} (w f : α → ℝ) {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hw : ∀ a, 0 ≤ w a)
    (hbuffer : ∀ a, f a ≤ B) :
    ∀ a, 0 ≤ affineCorrection w f M B a := by
  intro a
  exact div_nonneg (add_nonneg (hw a) (div_nonneg (sub_nonneg.mpr (hbuffer a)) hM.le))
    (by linarith)

theorem affineCorrection_mass {α : Type*} [Fintype α]
    (w f : α → ℝ) {M B : ℝ} (hM : 0 < M) (hB : 0 ≤ B)
    (hcard : (Fintype.card α : ℝ) = M)
    (hmass : ∑ a, w a = 1) (hf : ∑ a, f a = 0) :
    (∑ a, affineCorrection w f M B a) = 1 := by
  have hbuffer : (∑ a, (B - f a) / M) = B := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hf, sub_zero]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hnum : (∑ a, (w a + (B - f a) / M)) = 1 + B := by
    rw [Finset.sum_add_distrib, hmass, hbuffer]
  calc
    _ = (∑ a, (w a + (B - f a) / M)) / (1 + B) := by
      unfold affineCorrection
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    _ = 1 := by rw [hnum, div_self (by linarith : 1 + B ≠ 0)]

theorem affineCorrection_moment {α : Type*} [Fintype α]
    (w f φ : α → ℝ) {M B : ℝ} (hM : 0 < M)
    (hφ : ∑ a, φ a = 0)
    (hcancel : (∑ a, f a * φ a) = M * (∑ a, w a * φ a)) :
    (∑ a, affineCorrection w f M B a * φ a) = 0 := by
  have hnum : (∑ a, (w a + (B - f a) / M) * φ a) = 0 := by
    have hterm : ∀ a, (w a + (B - f a) / M) * φ a =
        w a * φ a + (B * φ a - f a * φ a) * M⁻¹ := by
      intro a
      rw [div_eq_mul_inv]
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hφ, mul_zero, zero_sub, hcancel]
    field_simp
    ring
  calc
    _ = (∑ a, (w a + (B - f a) / M) * φ a) / (1 + B) := by
      unfold affineCorrection
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [hnum, zero_div]

theorem affineCorrection_dominates_scaled {α : Type*} (w f : α → ℝ) {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hbuffer : ∀ a, f a ≤ B) :
    ∀ a, w a / (1 + B) ≤ affineCorrection w f M B a := by
  intro a
  unfold affineCorrection
  apply (div_le_div_iff_of_pos_right (by linarith : 0 < 1 + B)).2
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr (hbuffer a)) hM.le)

theorem affineCorrection_collision_lower {α : Type*} [Fintype α]
    (w f : α → ℝ) {M B : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hw : ∀ a, 0 ≤ w a)
    (hbuffer : ∀ a, f a ≤ B) :
    collision w / (1 + B) ^ 2 ≤ collision (affineCorrection w f M B) := by
  have hq := affineCorrection_nonneg w f hM hB hw hbuffer
  have hdom := affineCorrection_dominates_scaled w f hM hB hbuffer
  have hsum : (∑ a, (w a / (1 + B)) ^ 2) ≤ collision (affineCorrection w f M B) := by
    apply Finset.sum_le_sum
    intro a _
    have hscaled : 0 ≤ w a / (1 + B) := div_nonneg (hw a) (by linarith)
    nlinarith [hdom a, hq a]
  have hid : (∑ a, (w a / (1 + B)) ^ 2) = collision w / (1 + B) ^ 2 := by
    simp_rw [div_pow, div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rfl
  rw [hid] at hsum
  exact hsum

theorem affineCorrection_collision_identity {α : Type*} [Fintype α]
    (w f : α → ℝ) {M B S : ℝ} (hM : 0 < M) (hB : 0 ≤ B)
    (hcard : (Fintype.card α : ℝ) = M) (hmass : ∑ a, w a = 1)
    (hf : ∑ a, f a = 0) (hweighted : (∑ a, w a * f a) = S)
    (hsquare : (∑ a, f a ^ 2) = M * S) :
    collision (affineCorrection w f M B) =
      1 / M + (collision w - (1 + S) / M) / (1 + B) ^ 2 := by
  have hden : 1 + B ≠ 0 := by linarith
  have hpoint : ∀ a, M ^ 2 * (1 + B) ^ 2 * affineCorrection w f M B a ^ 2 =
      M ^ 2 * w a ^ 2 + (2 * M * B) * w a - (2 * M) * (w a * f a) +
        B ^ 2 - (2 * B) * f a + f a ^ 2 := by
    intro a
    unfold affineCorrection
    field_simp
    ring
  have hsum := Finset.sum_congr rfl
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  simp_rw [← Finset.mul_sum] at hsum
  simp only [hmass, hf, hweighted, hsquare, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard, mul_one, mul_zero, sub_zero] at hsum
  change M ^ 2 * (1 + B) ^ 2 * collision (affineCorrection w f M B) =
    M ^ 2 * collision w + 2 * M * B - 2 * M * S + M * B ^ 2 + M * S at hsum
  apply (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hM.ne') (pow_ne_zero 2 hden)))
  field_simp
  nlinarith [hsum]

theorem affineCorrection_variation_bound {α : Type*} [Fintype α]
    (w f : α → ℝ) {M B : ℝ} (hM : 0 < M) (hB : 0 ≤ B)
    (hcard : (Fintype.card α : ℝ) = M)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hf : ∑ a, f a = 0) (hbuffer : ∀ a, f a ≤ B) :
    (1 / 2 : ℝ) * (∑ a, |affineCorrection w f M B a - w a|) ≤ B / (1 + B) := by
  have hden : 0 < 1 + B := by linarith
  have hbufferSum : (∑ a, (B - f a) / M) = B := by
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hf, sub_zero]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hterm : ∀ a, |affineCorrection w f M B a - w a| ≤
      ((B - f a) / M + B * w a) / (1 + B) := by
    intro a
    have hg : 0 ≤ (B - f a) / M := div_nonneg (sub_nonneg.mpr (hbuffer a)) hM.le
    have hbw : 0 ≤ B * w a := mul_nonneg hB (hw a)
    have hid : affineCorrection w f M B a - w a =
        ((B - f a) / M - B * w a) / (1 + B) := by
      unfold affineCorrection
      field_simp
      ring
    rw [hid, abs_div, abs_of_pos hden]
    apply (div_le_div_iff_of_pos_right hden).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsum := Finset.sum_le_sum
    (fun a (_ : a ∈ (Finset.univ : Finset α)) => hterm a)
  rw [← Finset.sum_div, Finset.sum_add_distrib, hbufferSum,
    ← Finset.mul_sum, hmass, mul_one] at hsum
  calc
    _ ≤ (1 / 2 : ℝ) * ((B + B) / (1 + B)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

theorem buffer_reciprocal_square_bound {B : ℝ} (hB : 0 ≤ B) :
    1 - 1 / (1 + B) ^ 2 ≤ 2 * B := by
  have hp : 0 < (1 + B) ^ 2 := sq_pos_of_pos (by linarith)
  apply (mul_le_mul_iff_left₀ hp).mp
  have hc : (1 - 1 / (1 + B) ^ 2) * (1 + B) ^ 2 = (1 + B) ^ 2 - 1 := by
    field_simp
  rw [hc]
  have hcube : 0 ≤ B ^ 3 := pow_nonneg hB _
  nlinarith [sq_nonneg B]

theorem correction_deficit_window {N B P Q : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (hP : 1 / N ≤ P) (hQ : P / (1 + B) ^ 2 ≤ Q)
    (hsmall : B ≤ 1 / (2048 * N ^ 3)) :
    1 / N - Q ≤ 1 / (1024 * N ^ 4) := by
  have hden : 0 < (1 + B) ^ 2 := sq_pos_of_pos (by linarith)
  have hq : (1 / N) / (1 + B) ^ 2 ≤ Q :=
    (div_le_div_of_nonneg_right hP hden.le).trans hQ
  have hbuffer := mul_le_mul_of_nonneg_left (buffer_reciprocal_square_bound hB)
    (le_of_lt (div_pos zero_lt_one hN))
  have hfirst : 1 / N - Q ≤ 2 * B / N := by
    have hid : (1 / N) * (1 - 1 / (1 + B) ^ 2) =
        1 / N - (1 / N) / (1 + B) ^ 2 := by ring
    rw [hid] at hbuffer
    calc
      _ ≤ 1 / N - (1 / N) / (1 + B) ^ 2 := by linarith
      _ ≤ (1 / N) * (2 * B) := hbuffer
      _ = _ := by ring
  have hsecond : 2 * B / N ≤ 2 * (1 / (2048 * N ^ 3)) / N :=
    div_le_div_of_nonneg_right (by linarith) hN.le
  have hid : 2 * (1 / (2048 * N ^ 3)) / N = 1 / (1024 * N ^ 4) := by
    field_simp
    ring
  exact hfirst.trans (hsecond.trans_eq hid)

end EntropyDesigns
