/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeTransfer.ScaledPowerGap
public import EntropyPrimeTransfer.OrderPowerScale
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
open Filter Asymptotics GapTransfer
open scoped Topology
noncomputable section

/-- Translate the transfer's two deficits and sharp distance to the full order.
All exponents are actual real powers in BigTheta, not informal annotations. -/
theorem polynomial_full_order_rates (θ : ℝ) (hθ : 0<θ) (S : ℕ)
    (k : ℕ → ℕ) (hk : ∀ i,0<k i)
    (hr : Tendsto (fun i => (k i:ℝ)/(2:ℝ)^(S+i)) atTop (nhds 1))
    (f g : ℕ → ℝ)
    (hf : f =Θ[atTop] (fun i => dyadicBuffer (scaledPowerGap θ) (S+i)/(2:ℝ)^(S+i)))
    (hg : g =Θ[atTop] (fun i => dyadicBuffer (scaledPowerGap θ) (S+i)/((2:ℝ)^(S+i))^3)) :
    (f =Θ[atTop] (fun i => ((k i:ℝ)*(2:ℝ)^(S+i))^((θ-1)/2))) ∧
    (g =Θ[atTop] (fun i => ((k i:ℝ)*(2:ℝ)^(S+i))^((θ-3)/2))) ∧
    ((fun i => 1/(k i:ℝ)) =Θ[atTop]
      (fun i => ((k i:ℝ)*(2:ℝ)^(S+i))^(-(1:ℝ)/2))) := by
  let H : ℕ → ℝ := fun i => (2:ℝ)^(S+i)
  have hH (i : ℕ) : 0<H i := pow_pos (by norm_num) _
  have hK (i : ℕ) : (0:ℝ)≤(k i:ℝ) := Nat.cast_nonneg _
  have hindex : Tendsto (fun i : ℕ => S+i) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_left i S) tendsto_id
  have hb0 := polynomial_buffer_isTheta θ hθ
  have hb : (fun i => dyadicBuffer (scaledPowerGap θ) (S+i))
      =Θ[atTop] (fun i => (H i)^θ) := by
    exact ⟨hb0.1.comp_tendsto hindex,hb0.2.comp_tendsto hindex⟩
  have hf1 : (fun i => dyadicBuffer (scaledPowerGap θ) (S+i)/H i)
      =Θ[atTop] (fun i => (H i)^θ/(H i)^(1:ℝ)) := by
    simpa only [Real.rpow_one] using hb.div (isTheta_refl H atTop)
  have hg1 : (fun i => dyadicBuffer (scaledPowerGap θ) (S+i)/(H i)^3)
      =Θ[atTop] (fun i => (H i)^θ/(H i)^(3:ℝ)) := by
    simpa only [Real.rpow_ofNat] using hb.div ((isTheta_refl H atTop).pow 3)
  have hkh : (fun i => (k i:ℝ)) =Θ[atTop] H :=
    (isTheta_of_div_tendsto_nhds_ne_zero hr (by norm_num)).symm
  have hinv : (fun i => 1/(k i:ℝ)) =Θ[atTop] (fun i => (H i)^(0:ℝ)/(H i)^(1:ℝ)) := by
    simpa only [Real.rpow_zero,Real.rpow_one] using
      (isTheta_refl (fun _ : ℕ => (1:ℝ)) atTop).div hkh
  refine ⟨hf.trans (hf1.trans (quotient_power_full_order _ H hK hH hr θ 1)),
    hg.trans (hg1.trans (quotient_power_full_order _ H hK hH hr θ 3)),?_⟩
  have ht := hinv.trans (quotient_power_full_order _ H hK hH hr 0 1)
  norm_num only [zero_sub] at ht
  simpa only [H,neg_div] using ht

end
end EntropyDesigns.PrimeTransfer
