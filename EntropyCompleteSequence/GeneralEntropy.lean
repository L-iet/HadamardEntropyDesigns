/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.RelativeSequence
open scoped BigOperators
noncomputable section

def renyiOffOne {A : Type*} [Fintype A] (w : A → ℝ) (α : ℝ) : ℝ :=
  Real.log (∑ x, (w x)^α) / (1-α)

theorem rpow_factor (x α : ℝ) (hx : 0 < x) : x^α = x*x^(α-1) := by
  have he : α = 1+(α-1) := by ring
  conv_lhs => rw [he]
  rw [Real.rpow_add hx, Real.rpow_one]

theorem positive_power_sum {A : Type*} [Fintype A] (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1) (α : ℝ) :
    0 < ∑ x, (w x)^α := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, 0 < w x := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_nonpos (fun x (_ : x ∈ (Finset.univ : Finset A)) => hn x)
    linarith
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hx α)
    (Finset.single_le_sum (fun y _ => Real.rpow_nonneg (hw y) α) (Finset.mem_univ x))

theorem renyi_lower_of_atom_cap {A : Type*} [Fintype A] (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hne : α ≠ 1)
    (hcap : ∀ x, w x ≤ 1/N) : Real.log N ≤ renyiOffOne w α := by
  classical
  have hc : 0 < 1/N := one_div_pos.mpr hN
  have hs : 0 < ∑ x, (w x)^α := positive_power_sum w hw hmass α
  have hlog : Real.log ((1/N)^ (α-1)) = Real.log N * (1-α) := by
    rw [Real.log_rpow hc]
    simp only [one_div, Real.log_inv]
    ring
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpoint (x : A) : w x * (1/N)^(α-1) ≤ (w x)^α := by
      by_cases hz : w x = 0
      · simp [hz, Real.zero_rpow hα.ne']
      · have hx : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hz)
        rw [rpow_factor (w x) α hx]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hx (hcap x) (by linarith)) (hw x)
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x)
    rw [← Finset.sum_mul, hmass, one_mul] at hsum
    have hlogs := Real.log_le_log (Real.rpow_pos_of_pos hc _) hsum
    rw [hlog] at hlogs
    exact (le_div_iff₀ (by linarith : 0 < 1-α)).mpr hlogs
  · have hpoint (x : A) : (w x)^α ≤ w x * (1/N)^(α-1) := by
      by_cases hz : w x = 0
      · simp [hz, Real.zero_rpow hα.ne']
      · have hx : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hz)
        rw [rpow_factor (w x) α hx]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hw x) (hcap x) (by linarith)) (hw x)
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset A)) => hpoint x)
    rw [← Finset.sum_mul, hmass, one_mul] at hsum
    have hlogs := Real.log_le_log hs hsum
    rw [hlog] at hlogs
    exact (le_div_iff_of_neg (by linarith : 1-α < 0)).mpr hlogs

end
end EntropyDesigns.RelativeSequence
