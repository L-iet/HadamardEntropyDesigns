/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPermutationCost.CentralBinomialAsymptotics
public import EntropyPermutationCost.CentralWindowComparison
@[expose] public section
namespace EntropyDesigns.PermutationCost
open Filter
open scoped Topology

 theorem half_index_dyadic_scale_bounds (d : ℕ) (hd : 2≤d) :
    ((4:ℝ)^(d/2)/Real.sqrt ((d/2:ℕ):ℝ))≤2*((2:ℝ)^d/Real.sqrt (d:ℝ)) ∧
    ((2:ℝ)^d/Real.sqrt (d:ℝ))≤2*((4:ℝ)^(d/2)/Real.sqrt ((d/2:ℕ):ℝ)) := by
  let k := d/2
  have hk : 1≤k := by dsimp [k];omega
  have hkpos : (0:ℝ)<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hdpos : (0:ℝ)<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
  have hsK := Real.sqrt_pos.mpr hkpos
  have hsD := Real.sqrt_pos.mpr hdpos
  have hfour : (4:ℝ)^k=(2:ℝ)^(2*k) := by rw [pow_mul];norm_num
  have hpowL : (4:ℝ)^k≤(2:ℝ)^d := by
    rw [hfour]
    exact pow_le_pow_right₀ (by norm_num) (show 2*k≤d by dsimp [k];omega)
  have hpowU : (2:ℝ)^d≤2*(4:ℝ)^k := by
    calc
      _≤(2:ℝ)^(2*k+1) := pow_le_pow_right₀ (by norm_num) (by dsimp [k];omega)
      _=_ := by rw [pow_succ,←hfour];ring
  have hrootL : Real.sqrt (k:ℝ)≤Real.sqrt (d:ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show k≤d by dsimp [k];omega)
  have hdk : (d:ℝ)≤4*(k:ℝ) := by
    exact_mod_cast (show d≤4*k by dsimp [k] at *;omega)
  have hrootU : Real.sqrt (d:ℝ)≤2*Real.sqrt (k:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hkpos.le]
  constructor
  · change (4:ℝ)^k/Real.sqrt (k:ℝ)≤2*((2:ℝ)^d/Real.sqrt (d:ℝ))
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hsK hsD).mpr
    have hh := mul_le_mul_of_nonneg_left hrootU (show (0:ℝ)≤4^k by positivity)
    have hp := mul_le_mul_of_nonneg_right hpowL hsK.le
    nlinarith
  · change (2:ℝ)^d/Real.sqrt (d:ℝ)≤2*((4:ℝ)^k/Real.sqrt (k:ℝ))
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hsD hsK).mpr
    have hh := mul_le_mul_of_nonneg_left hrootL (show (0:ℝ)≤2*4^k by positivity)
    have hp := mul_le_mul_of_nonneg_right hpowU hsK.le
    nlinarith

 theorem half_index_dyadic_scale_isTheta :
    (fun d : ℕ => (4:ℝ)^(d/2)/Real.sqrt ((d/2:ℕ):ℝ)) =Θ[atTop]
      (fun d : ℕ => (2:ℝ)^d/Real.sqrt (d:ℝ)) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (2:ℕ)] with d hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤4^(d/2)/Real.sqrt ((d/2:ℕ):ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ)≤2^d/Real.sqrt (d:ℝ))] using (half_index_dyadic_scale_bounds d hd).1
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (2:ℕ)] with d hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤4^(d/2)/Real.sqrt ((d/2:ℕ):ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ)≤2^d/Real.sqrt (d:ℝ))] using (half_index_dyadic_scale_bounds d hd).2

 theorem half_index_central_binomial_isTheta :
    (fun d : ℕ => (Nat.centralBinom (d/2):ℝ)) =Θ[atTop]
      (fun d : ℕ => (2:ℝ)^d/Real.sqrt (d:ℝ)) := by
  have ht : Tendsto (fun d : ℕ => d/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨2*b,fun d hd => by omega⟩
  exact (central_binomial_isTheta.comp_tendsto ht).trans half_index_dyadic_scale_isTheta

 theorem symmetric_run_count_isTheta_central_binomial :
    (fun d : ℕ => (symmetricRunCount d:ℝ)) =Θ[atTop]
      (fun d : ℕ => (Nat.centralBinom (d/2):ℝ)) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (16:ℕ)] with d hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (symmetricRunCount d) (α:=ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (Nat.centralBinom (d/2)) (α:=ℝ))] using (symmetric_run_count_central_binomial_bounds hd).2
  · apply Asymptotics.IsBigO.of_bound (Real.exp 2)
    filter_upwards [eventually_ge_atTop (16:ℕ)] with d hd
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (symmetricRunCount d) (α:=ℝ)),
      abs_of_nonneg (Nat.cast_nonneg (Nat.centralBinom (d/2)) (α:=ℝ))] using (symmetric_run_count_central_binomial_bounds hd).1

 theorem full_permutation_symmetry_exponential_cost :
    (fun d : ℕ => (symmetricRunCount d:ℝ)) =Θ[atTop]
      (fun d : ℕ => (2:ℝ)^d/Real.sqrt (d:ℝ)) :=
  symmetric_run_count_isTheta_central_binomial.trans half_index_central_binomial_isTheta

end EntropyDesigns.PermutationCost
