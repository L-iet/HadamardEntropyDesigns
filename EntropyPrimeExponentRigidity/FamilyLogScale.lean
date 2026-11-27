/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeExponentRigidity.InfiniteFibers
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section
open Filter

def orderLogLog (k : ℕ) : ℝ := Real.log (Real.log (primePowerOrder k:ℝ))

theorem prime_power_order_log_upper (k : ℕ) (hk : 1≤k) :
    Real.log (primePowerOrder k:ℝ)≤2*(k:ℝ)*Real.log 3 := by
  have hpow : 0<3^k := pow_pos (by decide) k
  have hN : primePowerOrder k≤3^(k+1) := by
    unfold primePowerOrder
    rw [pow_succ]
    omega
  have hNpos : (0:ℝ)<(primePowerOrder k:ℝ) := by
    exact_mod_cast (show 0<primePowerOrder k by unfold primePowerOrder;omega)
  have hNcast : (primePowerOrder k:ℝ)≤(3:ℝ)^(k+1) := by exact_mod_cast hN
  have hL := Real.log_le_log hNpos hNcast
  rw [Real.log_pow] at hL
  push_cast at hL
  have hkR : (1:ℝ)≤(k:ℝ) := by exact_mod_cast hk
  have hlog3 : 0<Real.log 3 := Real.log_pos (by norm_num)
  exact hL.trans (mul_le_mul_of_nonneg_right (show (k:ℝ)+1≤2*(k:ℝ) by linarith) hlog3.le)

theorem prime_parameter_log_lower (k : ℕ) (hk : k.Prime) (hko : Odd k) :
    orderLogLog k-abs (Real.log (Real.log 3))≤
      Real.log ((primePowerOddParameter k).minFac:ℝ) := by
  obtain ⟨hfour,hmOdd,hm,hres⟩ := prime_power_parameter_properties k hk hko
  have hrough := prime_power_parameter_roughness k hk hko
  have hN : (1:ℝ)<(primePowerOrder k:ℝ) := by
    exact_mod_cast (show 1<primePowerOrder k by omega)
  have hp : (0:ℝ)<((primePowerOddParameter k).minFac:ℝ) := by
    exact_mod_cast (show 0<(primePowerOddParameter k).minFac by omega)
  have hlogN : 0<Real.log (primePowerOrder k:ℝ) := Real.log_pos hN
  have hlog3 : 0<Real.log 3 := Real.log_pos (by norm_num)
  have hpk : 2*(k:ℝ)≤((primePowerOddParameter k).minFac:ℝ) := by
    exact_mod_cast (show 2*k≤(primePowerOddParameter k).minFac by omega)
  have hupper := (prime_power_order_log_upper k hk.one_lt.le).trans
    (mul_le_mul_of_nonneg_right hpk hlog3.le)
  have h := Real.log_le_log hlogN hupper
  rw [Real.log_mul hp.ne' hlog3.ne'] at h
  change orderLogLog k≤Real.log ((primePowerOddParameter k).minFac:ℝ)+Real.log (Real.log 3) at h
  linarith [le_abs_self (Real.log (Real.log 3))]

theorem prime_power_order_tendsto :
    Tendsto (fun k : ℕ => (primePowerOrder k:ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  obtain ⟨N,hN⟩ : ∃ N : ℕ,b<(N:ℝ) := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with k hk
  exact hN.le.trans (show (N:ℝ)≤(primePowerOrder k:ℝ) by
    exact_mod_cast hk.trans (Nat.le_of_lt (exponent_lt_prime_power_order k)))

theorem order_loglog_tendsto : Tendsto orderLogLog atTop atTop := by
  change Tendsto (fun k : ℕ => Real.log (Real.log (primePowerOrder k:ℝ))) atTop atTop
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp prime_power_order_tendsto)

theorem eventual_log_threshold_inputs (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → k.Prime → Odd k →
      0<orderLogLog k ∧ 2<Real.log (orderLogLog k) ∧
      (1-epsilon/4)*orderLogLog k≤Real.log ((primePowerOddParameter k).minFac:ℝ) := by
  have hs := order_loglog_tendsto
  have hlogs := Real.tendsto_log_atTop.comp hs
  have hE : ∀ᶠ k : ℕ in atTop,0<orderLogLog k ∧
      2<Real.log (orderLogLog k) ∧
      4*abs (Real.log (Real.log 3))/epsilon≤orderLogLog k := by
    filter_upwards [hs.eventually (eventually_gt_atTop 0),
      hlogs.eventually (eventually_gt_atTop 2),
      hs.eventually (eventually_ge_atTop (4*abs (Real.log (Real.log 3))/epsilon))]
      with k h0 h2 hC
    exact ⟨h0,h2,hC⟩
  obtain ⟨K,hK⟩ := eventually_atTop.1 hE
  refine ⟨K,?_⟩
  intro k hk hprime hodd
  obtain ⟨h0,h2,hC⟩ := hK k hk
  refine ⟨h0,h2,?_⟩
  have hm := (div_le_iff₀ hepsilon).mp hC
  have hr := prime_parameter_log_lower k hprime hodd
  nlinarith

end
end EntropyDesigns.PrimeExponentRigidity
