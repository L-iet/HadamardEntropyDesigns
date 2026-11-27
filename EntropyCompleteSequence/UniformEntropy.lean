/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCompleteSequence.GeneralEntropy
public import EntropyDesigns.UniformEquality
@[expose] public section
namespace EntropyDesigns.RelativeSequence
open scoped BigOperators
noncomputable section

theorem uniform_power_sum {A : Type*} [Fintype A] (w : A → ℝ)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) :
    (∑ x, (w x)^α) = (1/N)^(α-1) := by
  have hpoint (x : A) : (w x)^α = w x * (1/N)^(α-1) := by
    rcases huniform x with hz | hc
    · simp [hz, Real.zero_rpow hα.ne']
    · rw [hc, rpow_factor (1/N) α (one_div_pos.mpr hN)]
  simp_rw [hpoint]
  rw [← Finset.sum_mul, hmass, one_mul]

theorem uniform_renyi {A : Type*} [Fintype A] (w : A → ℝ)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hne : α ≠ 1)
    (hmass : ∑ x, w x = 1) (huniform : ∀ x, w x = 0 ∨ w x = 1/N) :
    renyiOffOne w α = Real.log N := by
  rw [renyiOffOne, uniform_power_sum w N α hN hα hmass huniform,
    Real.log_rpow (one_div_pos.mpr hN)]
  simp only [one_div, Real.log_inv]
  have hh : 1-α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  apply (div_eq_iff hh).mpr
  ring

theorem uniform_shannon {A : Type*} [Fintype A] (w : A → ℝ)
    (N : ℝ) (hN : 0 < N) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) : shannon w = Real.log N :=
  (entropy_of_uniform_weights w hN hmass huniform).2.2

end
end EntropyDesigns.RelativeSequence
