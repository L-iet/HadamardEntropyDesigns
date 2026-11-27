/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.PermutationCost
open Filter
open scoped Topology

 theorem central_binomial_stirling_identity (n : ℕ) (hn : 0<n) :
    (Nat.centralBinom n:ℝ)*Real.sqrt (n:ℝ)/(4:ℝ)^n=
      Stirling.stirlingSeq (2*n)/(Stirling.stirlingSeq n)^2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hfact : (0:ℝ)<(n.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hs : Real.sqrt (n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  have hs2 := Real.sq_sqrt hnR.le
  have hfn : (Nat.centralBinom n:ℝ)*(n.factorial:ℝ)^2=((2*n).factorial:ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n≤2*n by omega)
    have he : 2*n-n=n := by omega
    rw [he] at h
    have h' : Nat.centralBinom n*n.factorial*n.factorial=(2*n).factorial := h
    exact_mod_cast (show Nat.centralBinom n*n.factorial^2=(2*n).factorial by nlinarith [h'])
  have hc : (Nat.centralBinom n:ℝ)=((2*n).factorial:ℝ)/(n.factorial:ℝ)^2 :=
    (eq_div_iff (pow_ne_zero 2 hfact.ne')).mpr hfn
  have hroot : Real.sqrt (2*((2*n:ℕ):ℝ))=2*Real.sqrt (n:ℝ) := by
    have he : 2*((2*n:ℕ):ℝ)=4*(n:ℝ) := by push_cast;ring
    rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]
  have hbase : (((2*n:ℕ):ℝ)/Real.exp 1)=2*((n:ℝ)/Real.exp 1) := by push_cast;ring
  have he : (0:ℝ)<(n:ℝ)/Real.exp 1 := div_pos hnR (Real.exp_pos 1)
  have hpow : (2:ℝ)^(2*n)=(4:ℝ)^n := by rw [pow_mul];norm_num
  rw [hc,Stirling.stirlingSeq,Stirling.stirlingSeq,hroot,hbase]
  simp only [div_pow,mul_pow]
  rw [Real.sq_sqrt (by positivity : (0:ℝ)≤2*(n:ℝ)),
    ←pow_mul,Nat.mul_comm n 2,hpow]
  field_simp [hs,hfact.ne',Real.exp_ne_zero 1,hnR.ne']
  all_goals simp only [hs2,←pow_mul,Nat.mul_comm n 2] <;> ring

 theorem central_binomial_scaled_limit :
    Tendsto (fun n : ℕ => (Nat.centralBinom n:ℝ)*Real.sqrt (n:ℝ)/(4:ℝ)^n)
      atTop (𝓝 (1/Real.sqrt Real.pi)) := by
  have h := Stirling.tendsto_stirlingSeq_sqrt_pi
  have ht : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by decide : 0<2)) tendsto_id
  have hp : Real.sqrt Real.pi≠0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hq := (h.comp ht).div (h.pow 2) (pow_ne_zero 2 hp)
  have he : Real.sqrt Real.pi/(Real.sqrt Real.pi)^2=1/Real.sqrt Real.pi := by
    field_simp
  rw [he] at hq
  apply hq.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact (central_binomial_stirling_identity n hn).symm

 theorem central_binomial_isTheta :
    (fun n : ℕ => (Nat.centralBinom n:ℝ)) =Θ[atTop]
      (fun n : ℕ => (4:ℝ)^n/Real.sqrt (n:ℝ)) := by
  have h := central_binomial_scaled_limit
  have h' : Tendsto (fun n : ℕ => (Nat.centralBinom n:ℝ)/
      ((4:ℝ)^n/Real.sqrt (n:ℝ))) atTop (𝓝 (1/Real.sqrt Real.pi)) := by
    convert h using 1
    ext n
    rw [div_div_eq_mul_div]
  exact (Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero h'
    (one_div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)))).symm

end EntropyDesigns.PermutationCost
