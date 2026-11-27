module

public import EntropyDesigns.FourierCorrection
public import EntropyDesigns.WalshCharacters

/-! # Finite orthogonal expansions for exact moment repair -/

@[expose] public section
namespace EntropyDesigns

def fourierPolynomial {α σ : Type*} [Fintype σ]
    (m : σ → ℝ) (φ : σ → α → ℝ) (a : α) : ℝ :=
  ∑ i, m i * φ i a

def fourierCoefficient {α σ : Type*} [Fintype α]
    (w : α → ℝ) (φ : σ → α → ℝ) (i : σ) : ℝ :=
  ∑ a, w a * φ i a

theorem fourierPolynomial_sum_zero {α σ : Type*} [Fintype α] [Fintype σ]
    (m : σ → ℝ) (φ : σ → α → ℝ) (hzero : ∀ i, ∑ a, φ i a = 0) :
    (∑ a, fourierPolynomial m φ a) = 0 := by
  unfold fourierPolynomial
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hzero, mul_zero]
  simp

theorem fourierPolynomial_cross {α σ : Type*}
    [Fintype α] [Fintype σ] [DecidableEq σ]
    (m : σ → ℝ) (φ : σ → α → ℝ) (M : ℝ)
    (horth : ∀ i j, ∑ a, φ i a * φ j a = if i = j then M else 0) (j : σ) :
    (∑ a, fourierPolynomial m φ a * φ j a) = M * m j := by
  unfold fourierPolynomial
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, m i * (∑ a, φ i a * φ j a) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = M * m j := by simp_rw [horth]; simp [mul_comm]

theorem fourierPolynomial_weighted {α σ : Type*} [Fintype α] [Fintype σ]
    (w : α → ℝ) (φ : σ → α → ℝ) :
    (∑ a, w a * fourierPolynomial (fourierCoefficient w φ) φ a) =
      ∑ i, fourierCoefficient w φ i ^ 2 := by
  unfold fourierPolynomial
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = fourierCoefficient w φ i * (∑ a, w a * φ i a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by rw [← fourierCoefficient]; ring

theorem fourierPolynomial_square {α σ : Type*}
    [Fintype α] [Fintype σ] [DecidableEq σ]
    (m : σ → ℝ) (φ : σ → α → ℝ) (M : ℝ)
    (horth : ∀ i j, ∑ a, φ i a * φ j a = if i = j then M else 0) :
    (∑ a, fourierPolynomial m φ a ^ 2) = M * (∑ i, m i ^ 2) := by
  calc
    _ = ∑ j, m j * (∑ a, fourierPolynomial m φ a * φ j a) := by
      conv_lhs => arg 2; ext a; rw [pow_two]; arg 2; unfold fourierPolynomial
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = M * (∑ i, m i ^ 2) := by
      simp_rw [fourierPolynomial_cross m φ M horth]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end EntropyDesigns
