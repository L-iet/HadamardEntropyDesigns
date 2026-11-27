module

public import EntropyDesigns.Collision

/-! # Weighted diagonal estimates and moment identities -/

@[expose] public section
namespace EntropyDesigns

/-- Expectation of a two-point kernel under two independent copies of a law. -/
def weightedTotal {α : Type*} [Fintype α] (w : α → ℝ) (P : α → α → ℝ) : ℝ :=
  ∑ a, ∑ b, w a * w b * P a b

theorem weightedTotal_eq {α : Type*} [Fintype α]
    (w : α → ℝ) (P : α → α → ℝ) :
    weightedTotal w P = ∑ a, w a * (∑ b, w b * P a b) := by
  unfold weightedTotal
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem weightedTotal_const {α : Type*} [Fintype α]
    (w : α → ℝ) (hmass : ∑ a, w a = 1) (c : ℝ) :
    weightedTotal w (fun _ _ => c) = c := by
  rw [weightedTotal_eq]
  simp_rw [← Finset.sum_mul, hmass, one_mul]

theorem weightedTotal_add {α : Type*} [Fintype α]
    (w : α → ℝ) (P Q : α → α → ℝ) :
    weightedTotal w (fun a b => P a b + Q a b) =
      weightedTotal w P + weightedTotal w Q := by
  simp [weightedTotal, mul_add, Finset.sum_add_distrib]

theorem weightedTotal_sub {α : Type*} [Fintype α]
    (w : α → ℝ) (P Q : α → α → ℝ) :
    weightedTotal w (fun a b => P a b - Q a b) =
      weightedTotal w P - weightedTotal w Q := by
  simp [weightedTotal, mul_sub, Finset.sum_sub_distrib]

theorem weightedTotal_smul {α : Type*} [Fintype α]
    (w : α → ℝ) (P : α → α → ℝ) (c : ℝ) :
    weightedTotal w (fun a b => c * P a b) = c * weightedTotal w P := by
  unfold weightedTotal
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem weightedTotal_rank_one {α : Type*} [Fintype α]
    (w ε : α → ℝ) :
    weightedTotal w (fun a b => ε a * ε b) = (∑ a, w a * ε a) ^ 2 := by
  unfold weightedTotal
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Retaining diagonal contributions in a nonnegative kernel bounds collision. -/
theorem weighted_diagonal_lower {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (d : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hP : ∀ a b, 0 ≤ P a b)
    (hdiag : ∀ a, P a a = d) :
    collision w * d ≤ weightedTotal w P := by
  unfold collision weightedTotal
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  calc
    w a ^ 2 * d = w a * w a * P a a := by rw [hdiag]; ring
    _ ≤ ∑ b, w a * w b * P a b :=
      Finset.single_le_sum
        (fun b _ => mul_nonneg (mul_nonneg (hw a) (hw b)) (hP a b))
        (Finset.mem_univ a)

theorem weightedTotal_of_pointwise_moment {α : Type*} [Fintype α]
    (w : α → ℝ) (P : α → α → ℝ) (n : ℝ)
    (hmass : ∑ a, w a = 1) (hmoment : ∀ a, ∑ b, w b * P a b = n) :
    weightedTotal w P = n := by
  rw [weightedTotal_eq]
  simp_rw [hmoment]
  rw [← Finset.sum_mul, hmass, one_mul]

theorem odd_dimension_collision_arithmetic {n C : ℝ} (hn : 1 < n)
    (hbound : C * (n ^ 2 - 1) ≤ n - 1) :
    C ≤ 1 / (n + 1) := by
  apply (le_div_iff₀ (by linarith : 0 < n + 1)).2
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < n - 1)).mp
  nlinarith

theorem residue_two_collision_arithmetic {n C : ℝ} (hn : 2 < n)
    (hbound : C * (n ^ 2 - 4) ≤ n - 2) :
    C ≤ 1 / (n + 2) := by
  apply (le_div_iff₀ (by linarith : 0 < n + 2)).2
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < n - 2)).mp
  nlinarith

theorem residue_one_collision_arithmetic {n C : ℝ} (hn : 1 < n)
    (hbound : C * (n ^ 2 + 2 * n - 3) ≤ n - 1) :
    C ≤ 1 / (n + 3) := by
  apply (le_div_iff₀ (by linarith : 0 < n + 3)).2
  apply (mul_le_mul_iff_left₀ (by linarith : 0 < n - 1)).mp
  nlinarith

end EntropyDesigns
