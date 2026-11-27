/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.PositiveWindows
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.RelativeSequence

theorem power_ratio_eq_exp (a s : ℕ) :
    ((12 ^ a : ℕ) : ℝ) / ((2 ^ s : ℕ) : ℝ) =
      Real.exp ((a : ℝ) * Real.log 12 - (s : ℝ) * Real.log 2) := by
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 12),
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem logarithm_window_order_bounds (a s : ℕ) (δ : ℝ)
    (hδ : δ < Real.log 2)
    (hlo : 0 < (s : ℝ) * Real.log 2 - (a : ℝ) * Real.log 12)
    (hhi : (s : ℝ) * Real.log 2 - (a : ℝ) * Real.log 12 < δ) :
    12 ^ a < 2 ^ s ∧ 2 ^ s < 2 * 12 ^ a := by
  have hpow12 : (0 : ℝ) < (12 : ℝ)^a := by positivity
  have hpow2 : (0 : ℝ) < (2 : ℝ)^s := by positivity
  have hlt : Real.log ((12 : ℝ)^a) < Real.log ((2 : ℝ)^s) := by
    rw [Real.log_pow, Real.log_pow]
    linarith
  have hlt' : Real.log ((2 : ℝ)^s) < Real.log (2 * (12 : ℝ)^a) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hpow12), Real.log_pow, Real.log_pow]
    linarith
  have hfirst : (12 : ℝ)^a < (2 : ℝ)^s := (Real.log_lt_log_iff hpow12 hpow2).mp hlt
  have hsecond : (2 : ℝ)^s < 2 * (12 : ℝ)^a :=
    (Real.log_lt_log_iff hpow2 (by positivity)).mp hlt'
  exact ⟨by exact_mod_cast hfirst, by exact_mod_cast hsecond⟩

end EntropyDesigns.RelativeSequence
