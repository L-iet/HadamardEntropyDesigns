/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeTransfer.PolynomialPrimeInput
public import EntropyGapTransfer.UniformTransfer
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
open Filter Set Asymptotics GapTransfer
open scoped Topology
noncomputable section

def scaledPowerGap (θ : ℝ) (x : ℝ) : ℝ := 2*(x/2)^θ

theorem scaled_power_sublinear (θ : ℝ) (hθ : θ<1) :
    scaledPowerGap θ =o[atTop] (fun x : ℝ => x) := by
  have hh := (power_gap_sublinear θ hθ).const_mul_left (2/(2:ℝ)^θ)
  apply hh.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  dsimp [scaledPowerGap]
  rw [Real.div_rpow hx (by norm_num)]
  ring

theorem scaled_power_nonnegative_monotone (θ : ℝ) (hθ : 0<θ) :
    (∀ x : ℝ,0≤x → 0≤scaledPowerGap θ x) ∧ MonotoneOn (scaledPowerGap θ) (Ici 0) := by
  constructor
  · intro x hx
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  · intro a ha b hb hab
    change 0≤a at ha
    change 0≤b at hb
    dsimp [scaledPowerGap]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Real.rpow_le_rpow (by linarith : 0≤a/2) (by linarith : a/2≤b/2) hθ.le

theorem polynomial_buffer_ratio (θ : ℝ) (hθ : 0<θ) :
    Tendsto (fun s : ℕ => dyadicBuffer (scaledPowerGap θ) s/((2:ℝ)^s)^θ)
      atTop (nhds (2/(2:ℝ)^θ)) := by
  have hb : (1:ℝ)<(2:ℝ)^θ := Real.one_lt_rpow (by norm_num) hθ
  have hs : Tendsto (fun s : ℕ => (s:ℝ)/((2:ℝ)^s)^θ) atTop (nhds 0) := by
    simpa only [pow_one,Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)] using
      tendsto_pow_const_div_const_pow_of_one_lt 1 hb
  have hi : Tendsto (fun s : ℕ => 1/((2:ℝ)^s)^θ) atTop (nhds 0) := by
    have ht := (tendsto_pow_atTop_atTop_of_one_lt hb).inv_tendsto_atTop
    change Tendsto (fun s : ℕ => (((2:ℝ)^θ)^s)⁻¹) atTop (nhds 0) at ht
    simpa only [one_div,Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)] using ht
  have he (s : ℕ) : scaledPowerGap θ ((2:ℝ)^s)/((2:ℝ)^s)^θ=2/(2:ℝ)^θ := by
    dsimp [scaledPowerGap]
    rw [Real.div_rpow (pow_nonneg (by norm_num) _) (by norm_num)]
    have hz : ((2:ℝ)^s)^θ≠0 := ne_of_gt (Real.rpow_pos_of_pos (pow_pos (by norm_num) _) _)
    field_simp
  have hc : Tendsto (fun s : ℕ => scaledPowerGap θ ((2:ℝ)^s)/((2:ℝ)^s)^θ)
      atTop (nhds (2/(2:ℝ)^θ)) := by simpa only [he] using tendsto_const_nhds
  simpa only [dyadicBuffer,add_div,add_zero] using (hc.add hs).add hi

theorem polynomial_buffer_isTheta (θ : ℝ) (hθ : 0<θ) :
    (fun s : ℕ => dyadicBuffer (scaledPowerGap θ) s)
      =Θ[atTop] (fun s : ℕ => ((2:ℝ)^s)^θ) := by
  exact (isTheta_of_div_tendsto_nhds_ne_zero (polynomial_buffer_ratio θ hθ)
    (div_ne_zero (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)))).symm

end
end EntropyDesigns.PrimeTransfer
