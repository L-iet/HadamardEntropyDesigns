/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.UniformBudget
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem dyadic_power_ratio_eq_exp (S s : ℕ) :
    (2:ℝ)^S/(2:ℝ)^s=Real.exp ((S:ℝ)*Real.log 2-(s:ℝ)*Real.log 2) := by
  rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]

theorem sublinear_dyadic_gap_ratio_zero (S : ℕ → ℕ)
    (hS : Tendsto (fun s => (S s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => (2:ℝ)^(S s)/(2:ℝ)^s) atTop (nhds 0) := by
  have hc : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := hS.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have he : Tendsto (fun s => (S s:ℝ)*Real.log 2-(s:ℝ)*Real.log 2) atTop atBot := by
    apply tendsto_atBot.2
    intro b
    have hlarge := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (-2*b/Real.log 2)
    filter_upwards [hsmall,hlarge,eventually_ge_atTop (1:ℕ)] with s hs hl hsn
    have hsp : (0:ℝ)<s := by exact_mod_cast (by omega : 0<s)
    have hbound : (S s:ℝ)≤(s:ℝ)/2 := by
      have hh := (div_lt_iff₀ hsp).mp hs
      linarith
    have hmul := mul_le_mul_of_nonneg_right hbound hc.le
    have hlast := (div_le_iff₀ hc).mp hl
    nlinarith
  have ht := Real.tendsto_exp_atBot.comp he
  simpa only [dyadic_power_ratio_eq_exp,Function.comp_def] using ht

theorem sublinear_dyadic_log_ratio_zero (S : ℕ → ℕ)
    (hS : Tendsto (fun s => (S s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => Real.log ((2:ℝ)^(S s))/Real.log ((2:ℝ)^s)) atTop (nhds 0) := by
  have he (s : ℕ) : Real.log ((2:ℝ)^(S s))/Real.log ((2:ℝ)^s)=(S s:ℝ)/(s:ℝ) := by
    rw [Real.log_pow,Real.log_pow]
    have hc : Real.log (2:ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
    by_cases hs : s=0
    · simp [hs]
    · have hsR : (s:ℝ)≠0 := by exact_mod_cast hs
      field_simp
  simpa only [he] using hS

theorem buffered_order_ratio_one (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => ((2^s-2^(bufferExponent T s):ℕ):ℝ)/(2:ℝ)^s) atTop (nhds 1) := by
  have hg := sublinear_dyadic_gap_ratio_zero (bufferExponent T) (buffer_exponent_ratio_zero T hT)
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub hg
  change Tendsto (fun s => 1-(2:ℝ)^(bufferExponent T s)/(2:ℝ)^s) atTop (nhds (1-0)) at ht
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [buffer_exponent_eventually_small T hT] with s hs
  have hle : (2:ℕ)^(bufferExponent T s)≤2^s :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.cast_sub hle,Nat.cast_pow,Nat.cast_pow,Nat.cast_ofNat,sub_div,div_self (ne_of_gt (pow_pos (by norm_num : (0:ℝ)<2) s))]

end
end EntropyDesigns.ProjectInstability
