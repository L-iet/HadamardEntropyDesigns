/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.SemigroupAsymptotics
public import HadamardMultibase.CoveringUpper
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open Filter
open scoped Topology

noncomputable def entropyTrialExponent (a k d : ℝ) (m : ℕ) : ℝ :=
  a*(m:ℝ)*Real.log m+k*(m:ℝ)*Real.log (Real.log m)+d*(m:ℝ)

noncomputable def entropyTrialOrder (a k d : ℝ) (m : ℕ) : ℕ :=
  ⌈Real.exp (entropyTrialExponent a k d m)⌉₊

 theorem entropy_base_scale_tendsto :
    Tendsto (fun m : ℕ => (m:ℝ)*Real.log m) atTop atTop := by
  have hm : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun m : ℕ => Real.log (m:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hm
  apply tendsto_atTop_mono' atTop ?_ hm
  filter_upwards [hl.eventually_ge_atTop (1:ℝ)] with m hlog
  have hp := mul_nonneg (Nat.cast_nonneg m (α:=ℝ)) (sub_nonneg.mpr hlog)
  nlinarith

 theorem entropy_trial_exponent_scaled_limit (a k d : ℝ) :
    Tendsto (fun m : ℕ => entropyTrialExponent a k d m/((m:ℝ)*Real.log m))
      atTop (𝓝 a) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun m : ℕ => Real.log (Real.log m)/Real.log m) atTop (𝓝 (0:ℝ)) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hc : Tendsto (fun m : ℕ => (1:ℝ)/Real.log m) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop hlog
  have hh : Tendsto (fun m : ℕ => a+(k*(Real.log (Real.log m)/Real.log m)+d*(1/Real.log m)))
      atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x:=a)).add ((hr.const_mul k).add (hc.const_mul d))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with m hm
  have hmR : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
  have hm0 : (m:ℝ)≠0 := by positivity
  have hl0 : Real.log (m:ℝ)≠0 := (Real.log_pos hmR).ne'
  dsimp [entropyTrialExponent]
  field_simp
  ring

 theorem entropy_trial_exponent_eventually_positive (a k d : ℝ) (ha : 0<a) :
    ∀ᶠ m : ℕ in atTop,0<entropyTrialExponent a k d m := by
  have hh := entropy_trial_exponent_scaled_limit a k d
  filter_upwards [(tendsto_order.mp hh).1 0 ha,eventually_ge_atTop (2:ℕ)] with m hratio hm
  have hmR : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
  have hp : (0:ℝ)<(m:ℝ)*Real.log m := mul_pos (by positivity) (Real.log_pos hmR)
  have he := (lt_div_iff₀ hp).mp hratio
  simpa using he

 theorem entropy_trial_log_order_bounds (a k d : ℝ) (ha : 0<a) :
    ∀ᶠ m : ℕ in atTop,entropyTrialExponent a k d m≤Real.log (entropyTrialOrder a k d m:ℝ) ∧
      Real.log (entropyTrialOrder a k d m:ℝ)≤entropyTrialExponent a k d m+Real.log 2 := by
  filter_upwards [entropy_trial_exponent_eventually_positive a k d ha] with m hm
  exact HadamardMultibase.log_ceil_exp_bounds hm.le

 theorem entropy_trial_log_order_scaled_limit (a k d : ℝ) (ha : 0<a) :
    Tendsto (fun m : ℕ => Real.log (entropyTrialOrder a k d m:ℝ)/((m:ℝ)*Real.log m))
      atTop (𝓝 a) := by
  have herr : Tendsto (fun m : ℕ =>
      (Real.log (entropyTrialOrder a k d m:ℝ)-entropyTrialExponent a k d m)/((m:ℝ)*Real.log m))
      atTop (𝓝 (0:ℝ)) := by
    have hupper : Tendsto (fun m : ℕ => Real.log (2:ℝ)/((m:ℝ)*Real.log m)) atTop (𝓝 (0:ℝ)) :=
      tendsto_const_nhds.div_atTop entropy_base_scale_tendsto
    apply squeeze_zero' ?_ ?_ hupper
    · filter_upwards [entropy_trial_log_order_bounds a k d ha,eventually_ge_atTop (2:ℕ)] with m hb hm
      apply div_nonneg (sub_nonneg.mpr hb.1)
      have hmR : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
      exact (mul_pos (by positivity : (0:ℝ)<m) (Real.log_pos hmR)).le
    · filter_upwards [entropy_trial_log_order_bounds a k d ha,eventually_ge_atTop (2:ℕ)] with m hb hm
      apply div_le_div_of_nonneg_right (by linarith :
        Real.log (entropyTrialOrder a k d m:ℝ)-entropyTrialExponent a k d m≤Real.log (2:ℝ))
      have hmR : (1:ℝ)<m := by exact_mod_cast (show 1<m by omega)
      exact (mul_pos (by positivity : (0:ℝ)<m) (Real.log_pos hmR)).le
  have hsum := (entropy_trial_exponent_scaled_limit a k d).add herr
  simpa only [add_zero] using hsum.congr (fun m => by ring)

 theorem entropy_trial_shifted_log_scaled_limit (a k d C : ℝ) (ha : 0<a) :
    Tendsto (fun m : ℕ => (Real.log (entropyTrialOrder a k d m:ℝ)+C)/((m:ℝ)*Real.log m))
      atTop (𝓝 a) := by
  have hc : Tendsto (fun m : ℕ => C/((m:ℝ)*Real.log m)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop entropy_base_scale_tendsto
  simpa only [add_zero] using ((entropy_trial_log_order_scaled_limit a k d ha).add hc).congr
    (fun m => by ring)

end EntropyDesigns.WeightedSimplex
