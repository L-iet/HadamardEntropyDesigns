/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.GrowthBounds
@[expose] public section
namespace EntropyDesigns.RelativeSequence

/-- Actual classical Hadamard orders just below powers of two, with enough
omitted slopes to contain an additive basis. This selects orders only;
the probability laws and their limiting entropy properties are separate. -/
theorem admissible_power_window (N : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδtwo : δ < Real.log 2) :
    ∃ a s : ℕ, N ≤ a ∧ s ≤ 2^s - 12^a ∧
      12^a < 2^s ∧ 2^s < 2 * 12^a ∧
      δ/2 < (s : ℝ)*Real.log 2 - (a : ℝ)*Real.log 12 ∧
      (s : ℝ)*Real.log 2 - (a : ℝ)*Real.log 12 < δ := by
  let c : ℝ := Real.exp (δ/2) - 1
  have hc : 0 < c := by
    dsimp [c]
    have := Real.exp_lt_exp.mpr (show (0 : ℝ) < δ/2 by linarith)
    rw [Real.exp_zero] at this
    linarith
  obtain ⟨M, hM⟩ := eventually_linear_le_twelve_power c hc
  obtain ⟨a, s, ha, hlo, hhi⟩ := positive_logarithm_window (max N M) δ hδ
  have hNa : N ≤ a := le_trans (le_max_left N M) ha
  have hMa : M ≤ a := le_trans (le_max_right N M) ha
  have hexp := Real.exp_lt_exp.mpr hlo
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 12)] at hexp
  have hscale := (lt_div_iff₀ (by positivity : (0 : ℝ) < (12 : ℝ)^a)).mp hexp
  have hlinear := hM a hMa
  have hsbound := logarithm_window_exponent_bound a s δ hδtwo hhi
  have hgap : (s : ℝ) < (2 : ℝ)^s - (12 : ℝ)^a := by
    dsimp [c] at hlinear
    nlinarith
  have hnat : s + 12^a ≤ 2^s := by
    have hh : (s : ℝ) + (12 : ℝ)^a ≤ (2 : ℝ)^s := by linarith
    exact_mod_cast hh
  have hs : s ≤ 2^s - 12^a := (Nat.le_sub_iff_add_le (by omega)).mpr hnat
  obtain ⟨hfirst, hsecond⟩ := logarithm_window_order_bounds a s δ hδtwo (by linarith) hhi
  exact ⟨a, s, hNa, hs, hfirst, hsecond, hlo, hhi⟩

end EntropyDesigns.RelativeSequence
