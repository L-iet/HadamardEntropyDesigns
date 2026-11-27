/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.PowerRatios
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.RelativeSequence

theorem quadratic_le_twelve_power (a : ℕ) : ((a : ℝ) + 1)^2 ≤ (12 : ℝ)^a := by
  induction a with
  | zero => norm_num
  | succ a ih =>
    rw [pow_succ (12 : ℝ) a]
    push_cast
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    nlinarith [sq_nonneg (a : ℝ)]

theorem eventually_linear_le_twelve_power (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ a : ℕ, N ≤ a → 4 * (a : ℝ) + 1 ≤ c * (12 : ℝ)^a := by
  obtain ⟨N, hN⟩ := exists_nat_gt (5 / c)
  refine ⟨max N 1, fun a ha => ?_⟩
  have hNa : N ≤ a := le_trans (le_max_left N 1) ha
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast le_trans (le_max_right N 1) ha
  have hca : 5 < c * (a : ℝ) := by
    have hlt : 5 / c < (a : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hNa)
    have := (div_lt_iff₀ hc).mp hlt
    linarith
  have hp := mul_le_mul_of_nonneg_left (quadratic_le_twelve_power a) hc.le
  nlinarith

theorem logarithm_window_exponent_bound (a s : ℕ) (δ : ℝ)
    (hδ : δ < Real.log 2)
    (hhi : (s : ℝ) * Real.log 2 - (a : ℝ) * Real.log 12 < δ) :
    (s : ℝ) < 4 * (a : ℝ) + 1 := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (12 : ℝ) < 4 * Real.log 2 := by
    have hh := Real.log_lt_log (by norm_num : (0 : ℝ) < 12)
      (by norm_num : (12 : ℝ) < 2^4)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hmul := mul_le_mul_of_nonneg_left hlog.le ha
  nlinarith

end EntropyDesigns.RelativeSequence
