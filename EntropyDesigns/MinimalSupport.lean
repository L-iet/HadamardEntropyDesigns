module

public import EntropyDesigns.CorrectionObstruction

/-! # Exact obstruction to reweighting a minimal-size support -/

@[expose] public section
namespace EntropyDesigns

theorem probability_card_collision_lower {α : Type*} [Fintype α]
    (w : α → ℝ) (hmass : ∑ a, w a = 1) :
    1 ≤ (Fintype.card α : ℝ) * collision w := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hmass] at h
  simpa only [collision, mul_comm, one_pow] using h

theorem minimal_support_uniform_rigidity {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (hcard : Fintype.card α ≤ roundedDimension n)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0) :
    Fintype.card α = roundedDimension n ∧
    (∀ a, w a = 1 / (roundedDimension n : ℝ)) ∧
    ∃ H : Matrix (Fin (roundedDimension n)) (Fin (roundedDimension n)) ℝ,
      Matrix.IsHadamard H := by
  classical
  have hN : 0 < roundedDimension n := by unfold roundedDimension; omega
  have hNR : (0 : ℝ) < roundedDimension n := by exact_mod_cast hN
  have hcardR : (Fintype.card α : ℝ) ≤ roundedDimension n := by exact_mod_cast hcard
  have hcollision : 0 ≤ collision w := Finset.sum_nonneg (fun a _ => sq_nonneg (w a))
  have hlower := probability_card_collision_lower w hmass
  have hlowerN : 1 / (roundedDimension n : ℝ) ≤ collision w := by
    apply (div_le_iff₀ hNR).2
    nlinarith
  have heq : collision w = 1 / (roundedDimension n : ℝ) :=
    le_antisymm (sharp_frame_collision_bound hn A w hsign hw hmass hiso) hlowerN
  have hsupport := sharp_frame_equality_support_card hn A w hsign hw hmass hiso heq
  have huniform := sharp_frame_equality_uniform hn A w hsign hw hmass hiso heq
  let G := Finset.univ.filter (fun a => w a ≠ 0)
  have hGcard : G.card = roundedDimension n := hsupport
  have hdim : Fintype.card α = roundedDimension n := by
    have hsub : G.card ≤ Fintype.card α :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)
    omega
  have hG : G = Finset.univ := Finset.eq_of_subset_of_card_le
    (Finset.filter_subset _ _) (by rw [Finset.card_univ, hdim, hGcard])
  have hnonzero : ∀ a, w a ≠ 0 := by
    intro a
    have ha : a ∈ G := by rw [hG]; simp
    exact (Finset.mem_filter.mp ha).2
  refine ⟨hdim, fun a => (huniform a).resolve_left (hnonzero a), ?_⟩
  obtain ⟨H, _, _, hH, _⟩ := equality_frame_hadamard_completion hn A w hsign hw hmass hiso heq
  exact ⟨H,hH⟩

theorem no_reweighting_of_failed_uniform_frame {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 3 ≤ n) (hcard : Fintype.card α = roundedDimension n)
    (A : α → Fin n → ℤ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hfailed : ¬∀ i j, (∑ a, (1 / (roundedDimension n : ℝ)) *
      (A a i : ℝ) * (A a j : ℝ)) = if i = j then 1 else 0) :
    ¬∃ w : α → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧
      (∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
        if i = j then 1 else 0) := by
  rintro ⟨w, hw, hmass, hiso⟩
  have hweights := (minimal_support_uniform_rigidity hn hcard.le A w hsign hw hmass hiso).2.1
  apply hfailed
  simpa only [hweights] using hiso

end EntropyDesigns
