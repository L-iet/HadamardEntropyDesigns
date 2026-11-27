module

public import EntropyDesigns.UniformEquality
public import EntropyDesigns.Completion.CodimensionThree

/-! # Actual Hadamard reconstruction from sharp collision equality -/

@[expose] public section
namespace EntropyDesigns
open Matrix

/-- Every equality frame embeds, with all original entries retained, into an
actual Hadamard matrix of the rounded order. The construction adds at most
three columns; the completion input is proved locally from scratch. -/
theorem equality_frame_hadamard_completion {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (heq : collision w = 1 / (roundedDimension n : ℝ)) :
    ∃ (H : Matrix (Fin (roundedDimension n)) (Fin (roundedDimension n)) ℝ)
      (columns : Fin n ↪ Fin (roundedDimension n))
      (rows : {a // w a ≠ 0} ≃ Fin (roundedDimension n)),
      Matrix.IsHadamard H ∧ ∀ a i, H (rows a) (columns i) = (A a i : ℝ) := by
  classical
  let S := {a // w a ≠ 0}
  let s := Finset.univ.filter (fun a => w a ≠ 0)
  have hcard : Fintype.card S = roundedDimension n := by
    dsimp [S]
    rw [Fintype.card_subtype]
    exact sharp_frame_equality_support_card hn A w hsign hw hmass hiso heq
  have hN : 0 < roundedDimension n := by unfold roundedDimension; omega
  let : Nonempty S := Fintype.card_pos_iff.mp (by rw [hcard]; exact hN)
  let P : Matrix (Fin n) S ℝ := fun i a => (A a i : ℝ)
  have hP : Completion.IsPartialHadamard P := by
    constructor
    · intro i a
      rcases hsign a i with h | h <;> simp [P, Completion.IsSign, h]
    · ext i j
      change (∑ a : S, (A a i : ℝ) * (A a j : ℝ)) =
        (Fintype.card S : ℝ) * (if i = j then 1 else 0)
      have hsum : (∑ a : S, (A a i : ℝ) * (A a j : ℝ)) =
          ∑ a ∈ s, (A a i : ℝ) * (A a j : ℝ) :=
        (Finset.sum_subtype s (fun a => by simp [s])
          (fun a => (A a i : ℝ) * (A a j : ℝ))).symm
      rw [hsum]
      have hg := sharp_frame_equality_support_gram hn A w hsign hw hmass hiso heq i j
      change (∑ a ∈ s, (A a i : ℝ) * (A a j : ℝ)) = _ at hg
      rw [hg, hcard]
      split_ifs <;> simp
  have hle : n ≤ roundedDimension n := by unfold roundedDimension; omega
  have hr : roundedDimension n - n ≤ 3 := by unfold roundedDimension; omega
  have hc : Fintype.card S = Fintype.card (Fin n) + (roundedDimension n - n) := by
    simp only [Fintype.card_fin, hcard]
    omega
  have hdiv : 4 ∣ Fintype.card S := by
    rw [hcard]
    exact ⟨(n + 3) / 4, rfl⟩
  obtain ⟨L, cols, hL, hret⟩ :=
    Completion.codimension_le_three_completion (roundedDimension n - n) hr hc hdiv P hP
  let e : S ≃ Fin (roundedDimension n) := Fintype.equivOfCardEq (by simpa using hcard)
  refine ⟨Matrix.reindex e e Lᵀ,
    ⟨fun i => e (cols i), e.injective.comp cols.injective⟩, e,
    hL.transpose.reindex e e, ?_⟩
  intro a i
  change L (e.symm (e (cols i))) (e.symm (e a)) = (A a i : ℝ)
  simpa only [e.symm_apply_apply, P] using hret i a

end EntropyDesigns
