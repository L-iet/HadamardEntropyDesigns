/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.EntropyScaleLimits
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped BigOperators Topology

noncomputable def entropyCountEnvelope (a k d C D : ℝ) (r m : ℕ) : ℝ :=
  (Real.log (entropyTrialOrder a k d m:ℝ)+C)^r/D+(m:ℝ)

 theorem entropy_linear_over_scale_power_limit (r : ℕ) (hr : 2≤r) :
    Tendsto (fun m : ℕ => (m:ℝ)/((m:ℝ)*Real.log m)^r) atTop (𝓝 (0:ℝ)) := by
  have hl : Tendsto (fun m : ℕ => Real.log (m:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun m : ℕ => (1:ℝ)/(m:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ hi
  · filter_upwards [hl.eventually_ge_atTop (1:ℝ),eventually_ge_atTop (1:ℕ)] with m hmL hm
    have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
    exact div_nonneg hmR.le (pow_nonneg (mul_nonneg hmR.le (by linarith)) _)
  · filter_upwards [hl.eventually_ge_atTop (1:ℝ),eventually_ge_atTop (1:ℕ)] with m hmL hm
    have hmR : (1:ℝ)≤m := by exact_mod_cast hm
    have hmpos : (0:ℝ)<m := by linarith
    have hscale : (m:ℝ)≤(m:ℝ)*Real.log m := by
      nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr hmL)]
    have hscaleone : (1:ℝ)≤(m:ℝ)*Real.log m := hmR.trans hscale
    have hpow : (m:ℝ)^2≤((m:ℝ)*Real.log m)^r :=
      (pow_le_pow_left₀ hmpos.le hscale 2).trans (pow_le_pow_right₀ hscaleone hr)
    have hp : (0:ℝ)<((m:ℝ)*Real.log m)^r := pow_pos (by linarith) _
    apply (div_le_div_iff₀ hp hmpos).mpr
    nlinarith

 theorem entropy_count_envelope_scaled_limit (a k d C D : ℝ) (r : ℕ)
    (hr : 2≤r) (ha : 0<a) :
    Tendsto (fun m : ℕ => entropyCountEnvelope a k d C D r m/((m:ℝ)*Real.log m)^r)
      atTop (𝓝 (a^r/D)) := by
  have hfirst := ((entropy_trial_shifted_log_scaled_limit a k d C ha).pow r).div_const D
  have hh := hfirst.add (entropy_linear_over_scale_power_limit r hr)
  simpa only [add_zero] using hh.congr (fun m => by
    dsimp [entropyCountEnvelope]
    rw [div_pow,add_div]
    ring)

 theorem entropy_count_envelope_log_limit (a k d C D : ℝ) (r : ℕ)
    (hr : 2≤r) (ha : 0<a) (hD : 0<D) :
    Tendsto (fun m : ℕ => Real.log (entropyCountEnvelope a k d C D r m)-
      (r:ℝ)*Real.log m-(r:ℝ)*Real.log (Real.log m))
      atTop (𝓝 ((r:ℝ)*Real.log a-Real.log D)) := by
  have hs := entropy_count_envelope_scaled_limit a k d C D r hr ha
  have hK : 0<a^r/D := div_pos (pow_pos ha _) hD
  have hh := (Real.continuousAt_log hK.ne').tendsto.comp hs
  have he : Real.log (a^r/D)=(r:ℝ)*Real.log a-Real.log D := by
    rw [Real.log_div (pow_ne_zero _ ha.ne') hD.ne',Real.log_pow]
  rw [he] at hh
  apply hh.congr'
  filter_upwards [(tendsto_order.mp hs).1 0 hK,eventually_ge_atTop (2:ℕ)] with m hpos hm
  have hmR : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
  have hm0 : (m:ℝ)≠0 := by positivity
  have hl := Real.log_pos hmR
  have hscale : (0:ℝ)<((m:ℝ)*Real.log m)^r := pow_pos (mul_pos (by positivity) hl) _
  have hV : 0<entropyCountEnvelope a k d C D r m := by
    have ht := (lt_div_iff₀ hscale).mp hpos
    simpa using ht
  simp only [Function.comp_apply]
  rw [Real.log_div hV.ne' hscale.ne',Real.log_pow,Real.log_mul hm0 hl.ne']
  ring

 theorem entropy_trial_order_positive (a k d : ℝ) (m : ℕ) :
    0<entropyTrialOrder a k d m := Nat.ceil_pos.mpr (Real.exp_pos _)

 theorem truncated_monoid_sharp_log_upper {r : ℕ} (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b) (N : ℕ) (hN : 1≤N) :
    ((HadamardMultibase.truncatedMonoid b N).card:ℝ)≤
      (Real.log (N:ℝ)+simplexShift b)^r/simplexDenominator b := by
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hh := (power_product_simplex_bounds b hb hind (Real.log (N:ℝ)) hlog).2
  rw [Real.exp_log hNR,power_count_nat_eq_truncated b hb N] at hh
  exact hh

 theorem entropy_trial_log_alphabet_upper {r : ℕ} (hr : 2≤r) (b : Fin r → ℕ)
    (hb : ∀ i,2≤b i) (hind : IndependentIntegerBases b)
    (a k d ε : ℝ) (ha : 0<a) (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log ((((HadamardMultibase.truncatedMonoid b (entropyTrialOrder a k d m)).card+m:ℕ):ℝ))≤
        (r:ℝ)*Real.log m+(r:ℝ)*Real.log (Real.log m)+
          (r:ℝ)*Real.log a-Real.log (simplexDenominator b)+ε := by
  have hl := entropy_count_envelope_log_limit a k d (simplexShift b) (simplexDenominator b)
    r hr ha (simplex_denominator_positive b hb)
  filter_upwards [(tendsto_order.mp hl).2
    ((r:ℝ)*Real.log a-Real.log (simplexDenominator b)+ε) (by linarith),
    eventually_ge_atTop (1:ℕ)] with m hlog hm
  have hN : 1≤entropyTrialOrder a k d m := by have hh := entropy_trial_order_positive a k d m;omega
  have hcount := truncated_monoid_sharp_log_upper b hb hind _ hN
  have hsum :
      (((HadamardMultibase.truncatedMonoid b (entropyTrialOrder a k d m)).card+m:ℕ):ℝ)≤
        entropyCountEnvelope a k d (simplexShift b) (simplexDenominator b) r m := by
    dsimp [entropyCountEnvelope]
    push_cast
    linarith
  have hp : (0:ℝ)<
      (((HadamardMultibase.truncatedMonoid b (entropyTrialOrder a k d m)).card+m:ℕ):ℝ) := by
    exact_mod_cast (show 0<(HadamardMultibase.truncatedMonoid b (entropyTrialOrder a k d m)).card+m by omega)
  have hh := Real.log_le_log hp hsum
  linarith

end EntropyDesigns.WeightedSimplex
