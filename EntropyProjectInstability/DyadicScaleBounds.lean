/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.BufferedUniform
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics
open scoped Topology
noncomputable section

/-- The original quantitative multiplier scale is sublinear in the dyadic exponent. -/
theorem dyadic_log_scale_ratio_zero :
    Tendsto (fun s : ℕ => (Real.log ((2:ℝ)^s)/Real.log (Real.log ((2:ℝ)^s)))/(s:ℝ))
      atTop (nhds 0) := by
  have hden : Tendsto (fun s : ℕ => Real.log (Real.log ((2:ℝ)^s))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp GapTransfer.dyadic_order_tends_infinity)
  have ht := hden.inv_tendsto_atTop.const_mul (Real.log 2)
  change Tendsto (fun s : ℕ => Real.log 2*(Real.log (Real.log ((2:ℝ)^s)))⁻¹)
    atTop (nhds (Real.log 2*0)) at ht
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with s hs
  have hsn : (s:ℝ)≠0 := by exact_mod_cast (by omega : s≠0)
  rw [Real.log_pow]
  field_simp <;> ring

/-- The ceiling binary logarithm is negligible compared with the exponent. -/
theorem ceiling_log_ratio_zero :
    Tendsto (fun s : ℕ => (Nat.clog 2 s:ℝ)/(s:ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun s : ℕ => Real.log (s:ℝ)/(s:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun s : ℕ => 1/(s:ℝ)) atTop (nhds 0) := by
    have ht := (tendsto_natCast_atTop_atTop (R:=ℝ)).inv_tendsto_atTop
    change Tendsto (fun s : ℕ => (s:ℝ)⁻¹) atTop (nhds 0) at ht
    simpa only [one_div] using ht
  have hup : Tendsto (fun s : ℕ => (Real.log (s:ℝ)/Real.log 2+1)/(s:ℝ)) atTop (nhds 0) := by
    have ht := (hlog.div_const (Real.log 2)).add hinv
    convert ht using 1 <;> try simp
    funext s
    ring
  apply squeeze_zero' (Eventually.of_forall (fun s => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) _ hup
  filter_upwards [eventually_ge_atTop (1:ℕ)] with s hs
  have hreal : (1:ℝ)≤s := by exact_mod_cast hs
  have hc := (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hreal)).le
  have he : ⌈Real.logb (2:ℝ) (s:ℝ)⌉₊=Nat.clog 2 s := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 s
  rw [he] at hc
  exact div_le_div_of_nonneg_right (by simpa only [Real.logb] using hc) (Nat.cast_nonneg _)

/-- The displayed maximum supplies the exact omitted-slope budget. -/
theorem ceiling_buffer_budget (s T : ℕ) : s≤2^(max T (Nat.clog 2 s)) := by
  exact (Nat.le_pow_clog (by decide : 1<2) s).trans
    (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

end
end EntropyDesigns.ProjectInstability
