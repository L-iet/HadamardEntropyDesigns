module

public import EntropyDesigns.NearUniformSupport
public import EntropyDesigns.HadamardEquality

/-! # Exact Hadamard extraction from a sufficiently small collision deficit -/

@[expose] public section
namespace EntropyDesigns

noncomputable def goodSupport {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (N : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter (fun a =>
    |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ)))

/-- The full explicit extraction theorem: exactly N good atoms, exact
uniformized isotropy, and an actual order-N Hadamard matrix. -/
theorem small_deficit_exact_extraction {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (hsmall : 1 / ((n : ℝ) + 3) - collision w ≤ 1 / (1024 * ((n : ℝ) + 3) ^ 4)) :
    (goodSupport w (n + 3)).card = n + 3 ∧
    (∀ i j, ∑ a, uniformOn (goodSupport w (n + 3)) (n + 3) a *
      (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) ∧
    ∃ H : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ, Matrix.IsHadamard H := by
  classical
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (0 : ℝ) < (n : ℝ) + 3 := by linarith
  have hdev := residue_frame_weight_deviation (by omega) hres A w hsign hw hmass hiso
  have hnum := extraction_numeric_window (by linarith : (8 : ℝ) ≤ (n : ℝ) + 3)
    (by nlinarith : ((n : ℝ) + 3) ^ 2 / 2 ≤ (n : ℝ) ^ 2 + 2 * n - 3)
    (residue_frame_deficit_nonneg (by omega) hres A w hsign hw hmass hiso) hsmall
  have herr : (∑ a, w a * |((n : ℝ) + 3) * w a - 1|) <
      1 / (8 * ((n : ℝ) + 3) ^ 2) := by
    rw [normalized_weight_error_identity w hN]
    exact (mul_le_mul_of_nonneg_left hdev hN.le).trans_lt hnum
  have herrNat : (∑ a, w a * |((n + 3 : ℕ) : ℝ) * w a - 1|) <
      1 / (8 * ((n + 3 : ℕ) : ℝ) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using herr
  have hc : (goodSupport w (n + 3)).card = n + 3 := by
    exact near_uniform_support_card w (n + 3) (by omega) hw hmass herrNat
  have hu : ∀ i j, ∑ a, uniformOn (goodSupport w (n + 3)) (n + 3) a *
      (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0 :=
    near_uniform_exact_isotropy A w (n + 3) (by omega) hsign hw hmass hiso herrNat
  refine ⟨hc, hu, ?_⟩
  have hrounded : roundedDimension n = n + 3 := by unfold roundedDimension; omega
  have hcoll : collision (uniformOn (goodSupport w (n + 3)) (n + 3)) =
      1 / (roundedDimension n : ℝ) := by
    rw [hrounded]
    exact uniformOn_collision _ _ (by omega) hc
  obtain ⟨H, _, _, hH, _⟩ := equality_frame_hadamard_completion (by omega) A
    (uniformOn (goodSupport w (n + 3)) (n + 3)) hsign (uniformOn_nonneg _ _)
    (uniformOn_mass _ _ (by omega) hc) hu hcoll
  rw [← hrounded]
  exact ⟨H, hH⟩

theorem no_hadamard_forces_strict_collision_gap {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (hno : ¬∃ H : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ, Matrix.IsHadamard H) :
    collision w < 1 / ((n : ℝ) + 3) - 1 / (1024 * ((n : ℝ) + 3) ^ 4) := by
  by_contra h
  have hsmall : 1 / ((n : ℝ) + 3) - collision w ≤
      1 / (1024 * ((n : ℝ) + 3) ^ 4) := by linarith [le_of_not_gt h]
  exact hno (small_deficit_exact_extraction hn hres A w hsign hw hmass hiso hsmall).2.2

theorem small_deficit_preserving_reconstruction {α : Type*}
    [Fintype α] [DecidableEq α]
    {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1)
    (A : α → Fin n → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, A a i = 1 ∨ A a i = -1)
    (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1)
    (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) =
      if i = j then 1 else 0)
    (hsmall : 1 / ((n : ℝ) + 3) - collision w ≤ 1 / (1024 * ((n : ℝ) + 3) ^ 4)) :
    roundedDimension n = n + 3 ∧
    ∃ (H : Matrix (Fin (roundedDimension n)) (Fin (roundedDimension n)) ℝ)
      (columns : Fin n ↪ Fin (roundedDimension n))
      (rows : {a // uniformOn (goodSupport w (n + 3)) (n + 3) a ≠ 0} ≃
        Fin (roundedDimension n)),
      Matrix.IsHadamard H ∧ ∀ a i, H (rows a) (columns i) = (A a i : ℝ) := by
  have hex := small_deficit_exact_extraction hn hres A w hsign hw hmass hiso hsmall
  have hr : roundedDimension n = n + 3 := by unfold roundedDimension; omega
  refine ⟨hr, ?_⟩
  exact equality_frame_hadamard_completion (by omega) A
    (uniformOn (goodSupport w (n + 3)) (n + 3)) hsign (uniformOn_nonneg _ _)
    (uniformOn_mass _ _ (by omega) hex.1) hex.2.1
    (by rw [hr]; exact uniformOn_collision _ _ (by omega) hex.1)

end EntropyDesigns
