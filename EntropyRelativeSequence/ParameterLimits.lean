/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.RelativeSequence
open Filter
open scoped Topology

theorem inverse_order_tends_zero (k h : ℕ → ℕ) (hk : ∀ i,0<k i)
    (hkh : ∀ i,k i<h i)
    (hratio : Tendsto (fun i => (k i:ℝ)/(h i:ℝ)) atTop (nhds 1)) :
    Tendsto (fun i => 1/(k i:ℝ)) atTop (nhds 0) := by
  have hhpos (i : ℕ) : (0:ℝ)<h i := by exact_mod_cast lt_trans (hk i) (hkh i)
  have hineq (i : ℕ) : (1:ℝ)/(h i:ℝ)≤1-(k i:ℝ)/(h i:ℝ) := by
    have hgap : (k i:ℝ)+1≤(h i:ℝ) := by exact_mod_cast Nat.succ_le_of_lt (hkh i)
    have h0 : (h i:ℝ)≠0 := (hhpos i).ne'
    apply (div_le_iff₀ (hhpos i)).2
    rw [sub_mul,one_mul,div_mul_cancel₀ _ h0]
    linarith
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hd : Tendsto (fun i => 1-(k i:ℝ)/(h i:ℝ)) atTop (nhds 0) := by
    simpa only [sub_self] using hc.sub hratio
  have hInvH : Tendsto (fun i => 1/(h i:ℝ)) atTop (nhds 0) :=
    squeeze_zero (fun i => div_nonneg (by norm_num) (Nat.cast_nonneg (h i))) hineq hd
  have hdiv := hInvH.div hratio (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun i => (1/(h i:ℝ))/((k i:ℝ)/(h i:ℝ))) atTop (nhds (0/1)) at hdiv
  have heq : (fun i : ℕ => (1/(h i:ℝ))/((k i:ℝ)/(h i:ℝ)))=(fun i => 1/(k i:ℝ)) := by
    funext i
    have hk0 : (k i:ℝ)≠0 := by exact_mod_cast (hk i).ne'
    have hh0 : (h i:ℝ)≠0 := (hhpos i).ne'
    field_simp
  rw [heq] at hdiv
  simpa only [zero_div] using hdiv

theorem sharp_distance_tends_one (k h : ℕ → ℕ) (hk : ∀ i,0<k i)
    (hkh : ∀ i,k i<h i)
    (hratio : Tendsto (fun i => (k i:ℝ)/(h i:ℝ)) atTop (nhds 1)) :
    Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) := by
  have hc : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa only [sub_zero] using hc.sub (inverse_order_tends_zero k h hk hkh hratio)

theorem entropy_scale_tends_zero (k h : ℕ → ℕ)
    (hratio : Tendsto (fun i => (k i:ℝ)/(h i:ℝ)) atTop (nhds 1)) :
    Tendsto (fun i => Real.log ((h i:ℝ)/(k i:ℝ))) atTop (nhds 0) := by
  have hlog : Tendsto (fun i => Real.log ((k i:ℝ)/(h i:ℝ))) atTop (nhds 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1:ℝ)≠0)).tendsto.comp hratio
  have heq : (fun i => Real.log ((h i:ℝ)/(k i:ℝ)))=(fun i => -Real.log ((k i:ℝ)/(h i:ℝ))) := by
    funext i
    rw [←inv_div,Real.log_inv]
  rw [heq]
  simpa only [neg_zero] using hlog.neg

theorem collision_deficit_identity {k h : ℕ} (hk : 0<k) (hh : 0<h) (hkh : k≤h) :
    1/((k*h:ℕ):ℝ)-1/((h^2:ℕ):ℝ)=((h-k:ℕ):ℝ)/((k*h^2:ℕ):ℝ) := by
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hh0 : (h:ℝ)≠0 := by exact_mod_cast hh.ne'
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hkh]
  field_simp <;> ring

end EntropyDesigns.RelativeSequence
