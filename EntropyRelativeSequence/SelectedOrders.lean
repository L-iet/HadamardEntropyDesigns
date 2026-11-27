/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.OrderWindows
public import EntropyRelativeSequence.TensorPowers
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
namespace EntropyDesigns.RelativeSequence
open Filter
open scoped Topology

/-- An unconditional sequence of actual classical Hadamard orders satisfying
the omitted-slope budget and approaching powers of two from below. -/
theorem selected_hadamard_orders :
    ∃ a s : ℕ → ℕ,
      (∀ i, i ≤ a i) ∧
      (∀ i, s i ≤ 2^(s i) - 12^(a i)) ∧
      (∀ i, 12^(a i) < 2^(s i) ∧ 2^(s i) < 2 * 12^(a i)) ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i))) (Fin (12^(a i))) ℤ,
        Matrix.IsHadamard H) ∧
      Tendsto (fun i => ((12^(a i) : ℕ) : ℝ) / ((2^(s i) : ℕ) : ℝ))
        atTop (nhds 1) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let δ : ℕ → ℝ := fun i => (Real.log 2 / 2) * (1/2 : ℝ)^i
  have hdpos (i : ℕ) : 0 < δ i := by dsimp [δ]; positivity
  have hdlt (i : ℕ) : δ i < Real.log 2 := by
    have hp : (1/2 : ℝ)^i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [δ]
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ Real.log (2 : ℝ)/2 by positivity)
    nlinarith
  have hex (i : ℕ) := admissible_power_window i (δ i) (hdpos i) (hdlt i)
  choose a s ha hgap hlt hhalf hlo hhi using hex
  refine ⟨a, s, ha, hgap, fun i => ⟨hlt i, hhalf i⟩,
    fun i => exists_hadamard_twelve_power (a i), ?_⟩
  have hp : Tendsto (fun i : ℕ => (1/2 : ℝ)^i) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd : Tendsto δ atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hp
  let err : ℕ → ℝ := fun i => (s i : ℝ)*Real.log 2 - (a i : ℝ)*Real.log 12
  have he : Tendsto err atTop (nhds 0) :=
    squeeze_zero (fun i => by dsimp [err]; linarith [hlo i, hdpos i])
      (fun i => le_of_lt (hhi i)) hd
  have heq : (fun i => ((12^(a i) : ℕ) : ℝ) / ((2^(s i) : ℕ) : ℝ)) =
      (fun i => Real.exp (-err i)) := by
    funext i
    rw [power_ratio_eq_exp]
    congr 1
    dsimp [err]
    ring
  rw [heq]
  simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp he.neg

end EntropyDesigns.RelativeSequence
