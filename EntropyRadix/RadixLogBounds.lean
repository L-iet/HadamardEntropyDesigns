/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns

theorem radix_base_gt_one {k : ℕ} (hk : 0<k) : 1<2^k := by
  cases k with
  | zero => omega
  | succ k =>
    rw [pow_succ]
    have hh : 0<2^k := by positivity
    omega

theorem radix_clog_real_log_bound {B q : ℕ} (hB : 1<B) (hq : 0<q) :
    (Nat.clog B (q+1):ℝ)≤Real.log (2*(q:ℝ)+1)/Real.log (B:ℝ)+1 := by
  let d := Nat.clog B (q+1)
  have hdpos : 0<d := Nat.clog_pos hB (by omega)
  have hp := Nat.pow_pred_clog_lt_self hB (by omega : 1<q+1)
  have hp' : B^d.pred<2*q+1 := lt_of_lt_of_le hp (by omega)
  have hpow : (B:ℝ)^d.pred<2*(q:ℝ)+1 := by exact_mod_cast hp'
  have hb : 0<(B:ℝ) := by exact_mod_cast (by omega : 0<B)
  have hl := Real.log_lt_log (by positivity : 0<(B:ℝ)^d.pred) hpow
  rw [Real.log_pow] at hl
  have hd : d.pred+1=d := Nat.succ_pred_eq_of_pos hdpos
  have hdR : (d.pred:ℝ)+1=(d:ℝ) := by exact_mod_cast hd
  have hlog : 0<Real.log (B:ℝ) := Real.log_pos (by exact_mod_cast hB)
  have hh : (d:ℝ)-1≤Real.log (2*(q:ℝ)+1)/Real.log (B:ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith
  change (d:ℝ)≤_
  linarith

theorem radix_finite_to_log_bound {k w q t : ℕ} (hk : 0<k) (hq : 0<q)
    (ht : t≤2*w*Nat.clog (2^k) (q+1)+2) :
    (t:ℝ)≤(2*(w:ℝ)/(k:ℝ))*(Real.log (2*(q:ℝ)+1)/Real.log 2)+2*(w:ℝ)+2 := by
  have hclog := radix_clog_real_log_bound (radix_base_gt_one hk) hq
  have hlogpow : Real.log ((2^k:ℕ):ℝ)=(k:ℝ)*Real.log 2 := by
    rw [Nat.cast_pow]
    exact Real.log_pow _ _
  rw [hlogpow] at hclog
  have htR : (t:ℝ)≤2*(w:ℝ)*(Nat.clog (2^k) (q+1):ℝ)+2 := by exact_mod_cast ht
  have hmul := mul_le_mul_of_nonneg_left hclog (by positivity : 0≤2*(w:ℝ))
  have hkR : 0<(k:ℝ) := by exact_mod_cast hk
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hid : 2*(w:ℝ)*(Real.log (2*(q:ℝ)+1)/((k:ℝ)*Real.log 2)+1)+2=
      (2*(w:ℝ)/(k:ℝ))*(Real.log (2*(q:ℝ)+1)/Real.log 2)+2*(w:ℝ)+2 := by
    field_simp
  rw [← hid]
  linarith

end EntropyDesigns
