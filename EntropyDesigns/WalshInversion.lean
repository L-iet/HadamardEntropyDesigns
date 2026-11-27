module

public import EntropyDesigns.WalshCharacters

/-! # Full finite Walsh inversion and Parseval identities -/

@[expose] public section
namespace EntropyDesigns

def maskSeed {d : ℕ} (S : Finset (Fin d)) (i : Fin d) : Bool := decide (i ∈ S)

def seedMask {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)

def maskSeedEquiv (d : ℕ) : Finset (Fin d) ≃ (Fin d → Bool) where
  toFun := maskSeed
  invFun := seedMask
  left_inv S := by
    ext i
    simp [maskSeed, seedMask]
  right_inv x := by
    funext i
    cases h : x i <;> simp [maskSeed, seedMask, h]

theorem walshChar_maskSeed {d : ℕ} (S T : Finset (Fin d)) :
    walshChar S (maskSeed T) = (-1 : ℤ) ^ (S ∩ T).card := by
  unfold walshChar
  have h : ∀ i, bitSign (maskSeed T i) = if i ∈ T then -1 else 1 := by
    intro i
    by_cases hi : i ∈ T <;> simp [maskSeed, bitSign, hi]
  simp_rw [h]
  simp

theorem walshChar_duality {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) :
    walshChar S x = walshChar (seedMask x) (maskSeed S) := by
  have hx : maskSeed (seedMask x) = x := (maskSeedEquiv d).apply_symm_apply x
  calc
    walshChar S x = walshChar S (maskSeed (seedMask x)) := by rw [hx]
    _ = walshChar (seedMask x) (maskSeed S) := by
      rw [walshChar_maskSeed, walshChar_maskSeed, Finset.inter_comm]

theorem walshChar_dual_orthogonality {d : ℕ} (x y : Fin d → Bool) :
    (∑ S : Finset (Fin d), walshChar S x * walshChar S y) =
      if x = y then (2 : ℤ) ^ d else 0 := by
  classical
  have hiff : seedMask x = seedMask y ↔ x = y := (maskSeedEquiv d).symm.injective.eq_iff
  calc
    _ = ∑ S : Finset (Fin d), walshChar (seedMask x) (maskSeed S) *
        walshChar (seedMask y) (maskSeed S) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [walshChar_duality S x, walshChar_duality S y]
    _ = ∑ z : Fin d → Bool, walshChar (seedMask x) z * walshChar (seedMask y) z :=
      Equiv.sum_comp (maskSeedEquiv d)
        (fun z => walshChar (seedMask x) z * walshChar (seedMask y) z)
    _ = _ := by
      rw [walshChar_orthogonality]
      simp only [hiff]

theorem walshChar_real_dual_orthogonality {d : ℕ} (x y : Fin d → Bool) :
    (∑ S : Finset (Fin d), (walshChar S x : ℝ) * (walshChar S y : ℝ)) =
      if x = y then (2 : ℝ) ^ d else 0 := by
  exact_mod_cast walshChar_dual_orthogonality x y

def walshCoefficient {d : ℕ} (w : (Fin d → Bool) → ℝ) (S : Finset (Fin d)) : ℝ :=
  ∑ x, w x * (walshChar S x : ℝ)

theorem walsh_inversion {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) :
    (∑ S : Finset (Fin d), walshCoefficient w S * (walshChar S x : ℝ)) = (2 : ℝ) ^ d * w x := by
  classical
  simp only [walshCoefficient, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, walshChar_real_dual_orthogonality]
  simp [mul_comm]

theorem walsh_parseval {d : ℕ} (w : (Fin d → Bool) → ℝ) :
    (∑ S : Finset (Fin d), walshCoefficient w S ^ 2) = (2 : ℝ) ^ d * collision w := by
  have hpoint : ∀ S : Finset (Fin d), walshCoefficient w S ^ 2 =
      ∑ x, w x * (walshCoefficient w S * (walshChar S x : ℝ)) := by
    intro S
    calc
      _ = walshCoefficient w S * ∑ x, w x * (walshChar S x : ℝ) := by
        rw [← walshCoefficient]
        ring
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, walsh_inversion]
  unfold collision
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem walsh_uniform_of_nonconstant_zero {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hmass : ∑ x, w x = 1)
    (hzero : ∀ S : Finset (Fin d), S.Nonempty → walshCoefficient w S = 0) :
    ∀ x, w x = 1 / (2 : ℝ) ^ d := by
  classical
  intro x
  have hsum : (∑ S : Finset (Fin d), walshCoefficient w S * (walshChar S x : ℝ)) = 1 := by
    rw [Finset.sum_eq_single ∅]
    · simp [walshCoefficient, walshChar, hmass]
    · intro S _ hS
      rw [hzero S (Finset.nonempty_iff_ne_empty.mpr hS), zero_mul]
    · simp
  rw [walsh_inversion] at hsum
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ d ≠ 0)).2
  linarith

end EntropyDesigns
