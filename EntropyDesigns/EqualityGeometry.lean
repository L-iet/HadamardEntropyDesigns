module

public import EntropyDesigns.UniformEquality

/-! # Off-diagonal geometry forced by collision equality -/

@[expose] public section
namespace EntropyDesigns

/-- Saturating a nonnegative diagonal estimate kills every off-diagonal kernel
entry between two nonzero-weight atoms. -/
theorem saturated_kernel_offdiagonal_zero {α : Type*}
    [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (d : ℝ)
    (hw : ∀ a, 0 ≤ w a) (hP : ∀ a b, 0 ≤ P a b)
    (hdiag : ∀ a, P a a = d)
    (heq : weightedTotal w P = collision w * d) :
    ∀ a b, w a ≠ 0 → w b ≠ 0 → a ≠ b → P a b = 0 := by
  let Q := fun a b => if a = b then (0 : ℝ) else w a * w b * P a b
  have hQ : ∀ a b, 0 ≤ Q a b := by
    intro a b
    dsimp [Q]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (hw a) (hw b)) (hP a b)
  have hsplit : ∀ a b, Q a b =
      w a * w b * P a b - if a = b then w a ^ 2 * d else 0 := by
    intro a b
    by_cases h : a = b
    · subst b
      simp only [Q, ite_true, hdiag]
      ring
    · simp [Q, h]
  have htotal : (∑ a, ∑ b, Q a b) = 0 := by
    simp_rw [hsplit, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    change weightedTotal w P - (∑ a, w a ^ 2 * d) = 0
    rw [← Finset.sum_mul]
    change weightedTotal w P - collision w * d = 0
    exact sub_eq_zero.mpr heq
  intro a b ha hb hab
  have hrow : (∑ b, Q a b) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => Finset.sum_nonneg (fun b _ => hQ a b))).mp
        htotal a (Finset.mem_univ a)
  have hentry : Q a b = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hQ a b)).mp
      hrow b (Finset.mem_univ b)
  simp only [Q, hab, ite_false] at hentry
  exact (mul_eq_zero.mp hentry).resolve_left (mul_ne_zero ha hb)

end EntropyDesigns
