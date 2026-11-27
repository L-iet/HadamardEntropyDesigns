module

public import EntropyDesigns.CharacterTilt

/-! # Exact half-cube supports at the two endpoint laws -/

@[expose] public section
namespace EntropyDesigns

def characterLevel {d : ℕ} (c : Finset (Fin d)) (e : ℤ) : Finset (Fin d → Bool) :=
  Finset.univ.filter (fun x => walshChar c x = e)

theorem characterLevel_double_card {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty)
    (e : ℤ) (he : e = 1 ∨ e = -1) : 2 * (characterLevel c e).card = 2 ^ d := by
  classical
  have hpoint : ∀ x, walshChar c x =
      e * (2 * (if walshChar c x = e then (1 : ℤ) else 0) - 1) := by
    intro x
    rcases he with rfl | rfl <;> rcases walshChar_sign c x with h | h <;> norm_num [h]
  have hboole : (∑ x : Fin d → Bool, if walshChar c x = e then (1 : ℤ) else 0) =
      (characterLevel c e).card := by simp [characterLevel]
  have hsum := walshChar_sum_zero c hc
  have hrewrite : (∑ x : Fin d → Bool, walshChar c x) =
      ∑ x : Fin d → Bool, e * (2 * (if walshChar c x = e then (1 : ℤ) else 0) - 1) := by
    apply Finset.sum_congr rfl
    intro x _
    exact hpoint x
  rw [hrewrite] at hsum
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hboole] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat] at hsum
  have hresult : 2 * ((characterLevel c e).card : ℤ) = (2 : ℤ) ^ d := by
    rcases he with rfl | rfl <;> nlinarith
  exact_mod_cast hresult

theorem characterLevel_card {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty)
    (e : ℤ) (he : e = 1 ∨ e = -1) : (characterLevel c e).card = 2 ^ d / 2 := by
  have h := characterLevel_double_card c hc e he
  omega

theorem characterTilt_endpoint_uniform {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty)
    (e : ℤ) (he : e = 1 ∨ e = -1) :
    (characterLevel c e).card = 2 ^ d / 2 ∧
      ∀ x, characterTilt c (e : ℝ) x =
        if x ∈ characterLevel c e then 1 / ((characterLevel c e).card : ℝ) else 0 := by
  classical
  have hdouble := characterLevel_double_card c hc e he
  have hM : (2 : ℝ) ^ d = 2 * ((characterLevel c e).card : ℝ) := by
    exact_mod_cast hdouble.symm
  have hpos : (0 : ℝ) < (characterLevel c e).card := by
    have : (0 : ℝ) < 2 ^ d := by positivity
    nlinarith
  have hratio : 2 / (2 : ℝ) ^ d = 1 / ((characterLevel c e).card : ℝ) := by
    rw [hM]
    field_simp
  refine ⟨characterLevel_card c hc e he, ?_⟩
  intro x
  have hpoint : characterTilt c (e : ℝ) x =
      if x ∈ characterLevel c e then 2 / (2 : ℝ) ^ d else 0 := by
    rcases he with rfl | rfl <;> rcases walshChar_sign c x with h | h <;>
      norm_num [characterTilt, characterLevel, h]
  rw [hpoint, hratio]

end EntropyDesigns
