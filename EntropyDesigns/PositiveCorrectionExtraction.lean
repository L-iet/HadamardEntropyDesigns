module

public import EntropyDesigns.PositiveCorrection
public import EntropyDesigns.ExactExtraction

/-! # Exact extraction after correction on a full-row-rank support -/

@[expose] public section
namespace EntropyDesigns

theorem supportCorrection_input_window {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] [DecidableEq α]
    {n : ℕ} (hn : 5 ≤ n) (hresidue : n % 4 = 1)
    (V : α → Fin n → ℤ) (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hsign : ∀ a i, V a i = 1 ∨ V a i = -1)
    (hcoordinates : ∀ i j, ∃ r, (∀ a, A r a = (V a i : ℝ) * (V a j : ℝ)) ∧
      b r = if i = j then 1 else 0)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1)
    (hA : A.rank = Fintype.card ι) (i₀ : ι)
    (hconstant : ∀ a, A i₀ a = 1) (hb : b i₀ = 1)
    (τ : ℝ) (hτ : 0 ≤ τ) (hres : ∀ i, |A.mulVec p i - b i| ≤ τ)
    (hmargin : ∀ a, supportCondition A * τ ≤ p a)
    (hcollision : 1 / ((n : ℝ) + 3) ≤ collision p)
    (hsmall : supportCondition A * τ ≤ 1 / (2048 * ((n : ℝ) + 3) ^ 4)) :
    ∃ H : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ, Matrix.IsHadamard H := by
  have hq := supportCorrection_nonneg A b p τ hτ hres hmargin
  have hmq := supportCorrection_mass A b p hA i₀ hconstant hb
  have hcorrect := supportCorrection_exact A b p hA
  have hiso : ∀ i j, ∑ a, supportCorrection A b p a * (V a i : ℝ) * (V a j : ℝ) =
      if i = j then 1 else 0 := by
    intro i j
    obtain ⟨r, hr, hbr⟩ := hcoordinates i j
    have h := congrFun hcorrect r
    simpa [Matrix.mulVec, dotProduct, hr, hbr, mul_comm, mul_left_comm, mul_assoc] using h
  have hlower := supportCorrection_collision_lower A b p hp hmass τ hτ hres
  have hdeficit : 1 / ((n : ℝ) + 3) - collision (supportCorrection A b p) ≤
      1 / (1024 * ((n : ℝ) + 3) ^ 4) := by
    have hscale : 2 * (1 / (2048 * ((n : ℝ) + 3) ^ 4)) =
        1 / (1024 * ((n : ℝ) + 3) ^ 4) := by
      have hpos : (0 : ℝ) < (n : ℝ) + 3 := by positivity
      field_simp
      ring
    rw [← hscale]
    nlinarith
  exact (small_deficit_exact_extraction hn hresidue V (supportCorrection A b p)
    hsign hq hmq hiso hdeficit).2.2

end EntropyDesigns
