module

public import EntropyDesigns.HadamardEquality
public import EntropyDesigns.HadamardLaws

/-! # Sharp entropy equality and its exact Hadamard-existence equivalence -/

@[expose] public section
namespace EntropyDesigns

/-- Full equality reconstruction for an actual unbiased pairwise-independent
Boolean-cube law, retaining every coordinate of every nonzero atom. -/
theorem sharp_sign_cube_equality_completion {d : ℕ} (hd : 2 ≤ d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hmass : ∑ b, w b = 1)
    (hmean : ∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0)
    (hpair : ∀ i j, i ≠ j →
      ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0)
    (heq : collision w = 1 / (roundedDimension (d + 1) : ℝ)) :
    (∀ b, w b = 0 ∨ w b = 1 / (roundedDimension (d + 1) : ℝ)) ∧
    (Finset.univ.filter (fun b => w b ≠ 0)).card = roundedDimension (d + 1) ∧
    ∃ (H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ)
      (columns : Fin (d + 1) ↪ Fin (roundedDimension (d + 1)))
      (rows : {b // w b ≠ 0} ≃ Fin (roundedDimension (d + 1))),
      Matrix.IsHadamard H ∧ ∀ b i,
        H (rows b) (columns i) =
          (augmentedSign (fun (b : Fin d → Bool) i => bitSign (b i))
            (b : Fin d → Bool) i : ℝ) := by
  classical
  let x := fun (b : Fin d → Bool) i => bitSign (b i)
  let A := augmentedSign x
  have hs : ∀ b i, x b i = 1 ∨ x b i = -1 := fun b i => bitSign_sign (b i)
  have hA := augmentedSign_sign x hs
  have hiso := augmentedSign_isotropic x w hs hmass hmean hpair
  exact ⟨sharp_frame_equality_uniform (by omega) A w hA hw hmass hiso heq,
    sharp_frame_equality_support_card (by omega) A w hA hw hmass hiso heq,
    equality_frame_hadamard_completion (by omega) A w hA hw hmass hiso heq⟩

theorem collision_entropy_equality_iff {α : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    {N : ℝ} (hN : 0 < N) :
    collisionEntropy w = Real.log N ↔ collision w = 1 / N := by
  constructor
  · intro h
    apply Real.log_injOn_pos (collision_pos w hw hmass) (div_pos zero_lt_one hN)
    have hl : Real.log (1 / N) = -Real.log N := by simp [one_div]
    rw [hl]
    unfold collisionEntropy at h
    linarith
  · intro h
    simp [collisionEntropy, h, one_div]

/-- Attainment of collision equality for an actual cube law is equivalent to
Hadamard existence at the rounded order. This does not assert attainment. -/
theorem collision_attainment_iff_hadamard {d : ℕ} (hd : 2 ≤ d) :
    (∃ w : (Fin d → Bool) → ℝ,
      (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧
      (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧
      (∀ i j, i ≠ j →
        ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧
      collision w = 1 / (roundedDimension (d + 1) : ℝ)) ↔
    ∃ H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ,
      Matrix.IsHadamard H := by
  constructor
  · rintro ⟨w, hw, hmass, hmean, hpair, heq⟩
    obtain ⟨H, _, _, hH, _⟩ :=
      (sharp_sign_cube_equality_completion hd w hw hmass hmean hpair heq).2.2
    exact ⟨H, hH⟩
  · rintro ⟨H, hH⟩
    obtain ⟨w, hw, hmass, hmean, hpair, hc, _, _⟩ := cube_law_of_hadamard hd H hH
    exact ⟨w, hw, hmass, hmean, hpair, hc⟩

/-- Attainment of either sharp entropy bound has the same exact existence
criterion; no conjectural matrix existence is assumed. -/
theorem entropy_attainment_iff_hadamard {d : ℕ} (hd : 2 ≤ d) :
    (∃ w : (Fin d → Bool) → ℝ,
      (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧
      (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧
      (∀ i j, i ≠ j →
        ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧
      (collisionEntropy w = Real.log (roundedDimension (d + 1)) ∨
        shannon w = Real.log (roundedDimension (d + 1)))) ↔
    ∃ H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ,
      Matrix.IsHadamard H := by
  have hN : (0 : ℝ) < roundedDimension (d + 1) := by
    have : 0 < roundedDimension (d + 1) := by unfold roundedDimension; omega
    exact_mod_cast this
  constructor
  · rintro ⟨w, hw, hmass, hmean, hpair, heq⟩
    apply (collision_attainment_iff_hadamard hd).1
    refine ⟨w, hw, hmass, hmean, hpair, ?_⟩
    rcases heq with h | h
    · exact (collision_entropy_equality_iff w hw hmass hN).1 h
    · exact shannon_equality_forces_collision_equality w hw hmass hN
        (sharp_sign_cube_entropy_bounds hd w hw hmass hmean hpair).1 h
  · rintro ⟨H, hH⟩
    obtain ⟨w, hw, hmass, hmean, hpair, _, h₂, _⟩ := cube_law_of_hadamard hd H hH
    exact ⟨w, hw, hmass, hmean, hpair, Or.inl h₂⟩

end EntropyDesigns
