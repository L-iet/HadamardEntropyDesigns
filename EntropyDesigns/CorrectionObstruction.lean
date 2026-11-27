module

public import EntropyDesigns.LowDegreeRepair

/-! # Quantized obstruction to guaranteed Fourier-buffer extraction -/

@[expose] public section
namespace EntropyDesigns

theorem lowCharacter_abs {d : ℕ} (i : LowIndex d) (x : Fin d → Bool) :
    |lowCharacter i x| = 1 := by
  rcases walshChar_sign i.val x with h | h <;> simp [lowCharacter,h]

/-- Each low-degree Fourier coefficient is at most twice the maximal buffer. -/
theorem coefficient_abs_le_twice_buffer {d : ℕ} (w : (Fin d → Bool) → ℝ) (i : LowIndex d) :
    |fourierCoefficient w lowCharacter i| ≤ 2 * correctionBuffer w := by
  let M : ℝ := 2 ^ d
  have hM : 0 < M := by dsimp [M]; positivity
  have hcross : (∑ x, lowPolynomial w x * lowCharacter i x) =
      M * fourierCoefficient w lowCharacter i :=
    fourierPolynomial_cross _ _ M lowCharacter_orthogonality i
  have hterm : ∀ x, |lowPolynomial w x| ≤ 2 * correctionBuffer w - lowPolynomial w x := by
    intro x
    apply abs_le.mpr
    constructor
    · linarith [correctionBuffer_nonneg w]
    · linarith [correctionBuffer_dominates w x]
  have hsum : (∑ x, |lowPolynomial w x|) ≤ M * (2 * correctionBuffer w) := by
    calc
      _ ≤ ∑ x, (2 * correctionBuffer w - lowPolynomial w x) :=
        Finset.sum_le_sum (fun x _ => hterm x)
      _ = _ := by
        rw [Finset.sum_sub_distrib, lowPolynomial_sum_zero, sub_zero]
        simp [M]
  have hbound : M * |fourierCoefficient w lowCharacter i| ≤
      M * (2 * correctionBuffer w) := by
    calc
      _ = |M * fourierCoefficient w lowCharacter i| := by rw [abs_mul, abs_of_pos hM]
      _ = |∑ x, lowPolynomial w x * lowCharacter i x| := by rw [hcross]
      _ ≤ ∑ x, |lowPolynomial w x * lowCharacter i x| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |lowPolynomial w x| := by simp_rw [abs_mul, lowCharacter_abs, mul_one]
      _ ≤ _ := hsum
  exact (mul_le_mul_iff_right₀ hM).mp hbound

/-- Uniform laws on an even number of sign rows have an even-integer moment numerator. -/
theorem uniform_sign_moment_quantized {α : Type*} [Fintype α] [DecidableEq α]
    (G : Finset α) (N : ℕ) (hcard : G.card = N) (heven : Even N)
    (p : α → ℤ) (hp : ∀ a, p a = 1 ∨ p a = -1) :
    ∃ z : ℤ, (∑ a, uniformOn G N a * (p a : ℝ)) = 2 * (z : ℝ) / (N : ℝ) := by
  classical
  have hEven : Even (Fintype.card G) := by simpa only [Fintype.card_coe, hcard] using heven
  have hsign : ∀ a : G, Completion.IsSign (p a : ℝ) := by
    intro a
    rcases hp a with h | h <;> simp [Completion.IsSign,h]
  obtain ⟨z, hz⟩ := Completion.sign_sum_even hEven (fun a : G => (p a : ℝ)) hsign
  have hsum : (∑ a ∈ G, (p a : ℝ)) = 2 * (z : ℝ) := by
    have hconvert : (∑ a ∈ G, (p a : ℝ)) = ∑ a : G, (p a : ℝ) :=
      Finset.sum_subtype G (fun _ => Iff.rfl) (fun a => (p a : ℝ))
    exact hconvert.trans hz
  refine ⟨z, ?_⟩
  unfold uniformOn
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [← Finset.mul_sum, hsum]
  ring

theorem nonzero_quantized_moment_lower {m : ℝ} {N : ℕ} (hN : 0 < N)
    (hquantized : ∃ z : ℤ, m = 2 * (z : ℝ) / (N : ℝ)) (hne : m ≠ 0) :
    2 / (N : ℝ) ≤ |m| := by
  obtain ⟨z, hz⟩ := hquantized
  have hzneq : z ≠ 0 := by
    intro h
    apply hne
    rw [hz,h]
    norm_num
  have hzabs : (1 : ℤ) ≤ |z| := by
    have : |z| ≠ 0 := abs_ne_zero.mpr hzneq
    have := abs_nonneg z
    omega
  have hzR : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hzabs
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hz,abs_div,abs_of_pos hNR,abs_mul]
  norm_num
  exact div_le_div_of_nonneg_right (by linarith) hNR.le

theorem cube_card_ge_twice_target {d : ℕ} (hd : 4 ≤ d) :
    2 * (d + 4) ≤ 2 ^ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hih := ih (by omega)
    rw [show 4 + (k + 1) = (4 + k) + 1 by omega, pow_succ]
    nlinarith

theorem uniform_cube_coefficient_lower {d N : ℕ}
    (G : Finset (Fin d → Bool)) (hcard : G.card = N) (hN : 0 < N) (heven : Even N)
    (i : LowIndex d) (hne : fourierCoefficient (uniformOn G N) lowCharacter i ≠ 0) :
    2 / (N : ℝ) ≤ |fourierCoefficient (uniformOn G N) lowCharacter i| := by
  apply nonzero_quantized_moment_lower hN _ hne
  exact uniform_sign_moment_quantized G N hcard heven (walshChar i.val)
    (walshChar_sign i.val)

theorem uniform_nonzero_moment_forces_buffer {d N : ℕ}
    (G : Finset (Fin d → Bool)) (hcard : G.card = N) (hN : 0 < N) (heven : Even N)
    (hnonzero : ∃ i : LowIndex d,
      fourierCoefficient (uniformOn G N) lowCharacter i ≠ 0) :
    1 / (N : ℝ) ≤ correctionBuffer (uniformOn G N) := by
  obtain ⟨i, hi⟩ := hnonzero
  have hlower := uniform_cube_coefficient_lower G hcard hN heven i hi
  have hupper := coefficient_abs_le_twice_buffer (uniformOn G N) i
  have hid : 2 / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
  rw [hid] at hlower
  linarith

theorem buffer_drop_lower {N B : ℝ} (hN : 2 ≤ N) (hB : 1 / N ≤ B) :
    1 / N ≤ 1 - 1 / (1 + B) ^ 2 := by
  have hNpos : 0 < N := by linarith
  have hcap : 0 < 1 / N := div_pos zero_lt_one hNpos
  have hBpos : 0 < B := lt_of_lt_of_le hcap hB
  have hden : 0 < (1 + 1 / N) ^ 2 := sq_pos_of_pos (by linarith)
  have hsq : (1 + 1 / N) ^ 2 ≤ (1 + B) ^ 2 := by nlinarith
  have hrecip := one_div_le_one_div_of_le hden hsq
  have hid : (1 - 1 / (1 + 1 / N) ^ 2) - 1 / N =
      (N ^ 2 - N - 1) / (N * (N + 1) ^ 2) := by
    field_simp
    ring
  have hnum : 0 ≤ N ^ 2 - N - 1 := by nlinarith
  have hbase : 0 ≤ (1 - 1 / (1 + 1 / N) ^ 2) - 1 / N := by
    rw [hid]
    exact div_nonneg hnum (by positivity)
  linarith

theorem large_cube_reciprocal_gap {N M : ℝ} (hN : 0 < N) (hM : 2 * N ≤ M) :
    1 / (2 * N) ≤ 1 / N - 1 / M := by
  have hc := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * N) hM
  have hid : 1 / N = 1 / (2 * N) + 1 / (2 * N) := by field_simp; ring
  linarith

theorem quantized_buffer_collision_gap {N M B S Q : ℝ}
    (hN : 2 ≤ N) (hM : 2 * N ≤ M) (hB : 1 / N ≤ B) (hS : 0 ≤ S)
    (hQ : Q = 1 / M + (1 / N - (1 + S) / M) / (1 + B) ^ 2) :
    1 / (2 * N ^ 2) ≤ 1 / N - Q := by
  have hNpos : 0 < N := by linarith
  have hMpos : 0 < M := by linarith
  have hBpos : 0 < B := lt_of_lt_of_le (div_pos zero_lt_one hNpos) hB
  have hden : 0 < (1 + B) ^ 2 := sq_pos_of_pos (by linarith)
  have hgap := large_cube_reciprocal_gap hNpos hM
  have hdrop := buffer_drop_lower hN hB
  have hgap_nonneg : 0 ≤ 1 / N - 1 / M :=
    (by positivity : (0 : ℝ) ≤ 1 / (2 * N)).trans hgap
  have hproduct := mul_le_mul hgap hdrop
    (by positivity : (0 : ℝ) ≤ 1 / N) hgap_nonneg
  have hidentity : (1 / N - Q) -
      (1 / N - 1 / M) * (1 - 1 / (1 + B) ^ 2) =
      S / (M * (1 + B) ^ 2) := by
    rw [hQ]
    field_simp
    ring
  have hnonneg : 0 ≤ S / (M * (1 + B) ^ 2) :=
    div_nonneg hS (mul_nonneg hMpos.le hden.le)
  have hbound : (1 / N - 1 / M) * (1 - 1 / (1 + B) ^ 2) ≤ 1 / N - Q := by
    linarith
  have hid : (1 / (2 * N)) * (1 / N) = 1 / (2 * N ^ 2) := by field_simp
  rw [hid] at hproduct
  exact hproduct.trans hbound

/-- A non-isotropic uniform candidate cannot enter the explicit extraction
window after the guaranteed maximal-buffer correction. -/
theorem uniform_candidate_correction_obstruction {d : ℕ}
    (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1)
    (G : Finset (Fin d → Bool)) (hcard : G.card = d + 4)
    (hnonzero : ∃ i : LowIndex d,
      fourierCoefficient (uniformOn G (d + 4)) lowCharacter i ≠ 0) :
    1 / (2 * ((d : ℝ) + 4) ^ 2) ≤
      1 / ((d : ℝ) + 4) - collision (correctedLaw (uniformOn G (d + 4))) := by
  have hN : 0 < d + 4 := by omega
  have heven : Even (d + 4) := ⟨(d + 4) / 2, by omega⟩
  have hb := uniform_nonzero_moment_forces_buffer G hcard hN heven hnonzero
  have hB : 1 / ((d : ℝ) + 4) ≤ correctionBuffer (uniformOn G (d + 4)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hb
  have hcube : 2 * ((d : ℝ) + 4) ≤ (2 : ℝ) ^ d := by
    exact_mod_cast cube_card_ge_twice_target hd
  have hf := correctedLaw_collision_identity (uniformOn G (d + 4))
    (uniformOn_mass G (d + 4) hN hcard)
  rw [uniformOn_collision G (d + 4) hN hcard] at hf
  simp only [Nat.cast_add, Nat.cast_ofNat] at hf
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  exact quantized_buffer_collision_gap (by linarith) hcube hB
    (Finset.sum_nonneg (fun i _ => sq_nonneg (fourierCoefficient
      (uniformOn G (d + 4)) lowCharacter i))) hf

theorem uniform_candidate_misses_extraction_window {d : ℕ}
    (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1)
    (G : Finset (Fin d → Bool)) (hcard : G.card = d + 4)
    (hnonzero : ∃ i : LowIndex d,
      fourierCoefficient (uniformOn G (d + 4)) lowCharacter i ≠ 0) :
    1 / (1024 * ((d : ℝ) + 4) ^ 4) <
      1 / ((d : ℝ) + 4) - collision (correctedLaw (uniformOn G (d + 4))) := by
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hN : (0 : ℝ) < (d : ℝ) + 4 := by linarith
  have hsq : 64 ≤ ((d : ℝ) + 4) ^ 2 := by nlinarith
  have hden : 2 * ((d : ℝ) + 4) ^ 2 < 1024 * ((d : ℝ) + 4) ^ 4 := by
    nlinarith [sq_nonneg (((d : ℝ) + 4) ^ 2 - 1)]
  have hgap := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < 2 * ((d : ℝ) + 4) ^ 2) hden
  exact hgap.trans_le (uniform_candidate_correction_obstruction hd hres G hcard hnonzero)

end EntropyDesigns
