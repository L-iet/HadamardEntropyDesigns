/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.RotationWindows
public import Mathlib.Tactic.Positivity
@[expose] public section
namespace EntropyDesigns.RelativeSequence

/-- Arbitrarily large powers of twelve lie just below a power of two
with a prescribed positive logarithmic separation. -/
theorem positive_logarithm_window (N : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ a s : ℕ, N ≤ a ∧
      δ / 2 < (s : ℝ) * Real.log 2 - (a : ℝ) * Real.log 12 ∧
      (s : ℝ) * Real.log 2 - (a : ℝ) * Real.log 12 < δ := by
  obtain ⟨a, ha, z, hlo, hhi⟩ :=
    logarithm_error_in_interval N (-δ) (-δ / 2) (by linarith)
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have htwelve : 0 < Real.log (12 : ℝ) := Real.log_pos (by norm_num)
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hzpos : (0 : ℝ) < z := by
    by_contra hn
    have hznonpos : (z : ℝ) ≤ 0 := le_of_not_gt hn
    have hzmul := mul_nonpos_of_nonpos_of_nonneg hznonpos htwo.le
    have hamul := mul_nonneg ha0 htwelve.le
    linarith
  have hz : (0 : ℤ) ≤ z := by exact_mod_cast hzpos.le
  have hs : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  refine ⟨a, z.toNat, ha, ?_, ?_⟩ <;> rw [hs] <;> linarith

end EntropyDesigns.RelativeSequence
