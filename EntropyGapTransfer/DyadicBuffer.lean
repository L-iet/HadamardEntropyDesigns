/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace EntropyDesigns.GapTransfer
open Filter Asymptotics
open scoped Topology

def dyadicBuffer (G : ℝ → ℝ) (s : ℕ) : ℝ := G ((2:ℝ)^s)+(s:ℝ)+1

theorem dyadic_order_tends_infinity : Tendsto (fun s : ℕ => (2:ℝ)^s) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

theorem dyadic_buffer_ratio_zero (G : ℝ → ℝ) (hG : G =o[atTop] (fun x : ℝ => x)) :
    Tendsto (fun s : ℕ => dyadicBuffer G s/(2:ℝ)^s) atTop (nhds 0) := by
  have hg : Tendsto (fun s : ℕ => G ((2:ℝ)^s)/(2:ℝ)^s) atTop (nhds 0) := by
    simpa only [Function.comp_def] using hG.tendsto_div_nhds_zero.comp dyadic_order_tends_infinity
  have hs : Tendsto (fun s : ℕ => (s:ℝ)/(2:ℝ)^s) atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have hi : Tendsto (fun s : ℕ => 1/(2:ℝ)^s) atTop (nhds 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
    simpa only [one_div_pow] using hh
  have hh := (hg.add hs).add hi
  simpa only [dyadicBuffer,add_div,zero_add] using hh

theorem dyadic_buffer_positive (G : ℝ → ℝ)
    (hG : ∀ x : ℝ,0≤x → 0≤G x) (s : ℕ) : 0<dyadicBuffer G s := by
  have hg := hG ((2:ℝ)^s) (pow_nonneg (by norm_num) _)
  have hs : (0:ℝ)≤s := Nat.cast_nonneg s
  dsimp [dyadicBuffer]
  linarith

theorem dyadic_buffer_eventually_small (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x)) :
    ∀ᶠ s : ℕ in atTop,3*dyadicBuffer G s<(2:ℝ)^s/2 := by
  have hh := (dyadic_buffer_ratio_zero G hG).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/6))
  filter_upwards [hh] with s hs
  have hp : (0:ℝ)<(2:ℝ)^s := pow_pos (by norm_num) _
  have hmul := (div_lt_iff₀ hp).mp hs
  linarith

theorem shifted_dyadic_tends_infinity (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) :
    Tendsto (fun s : ℕ => (2:ℝ)^s-2*dyadicBuffer G s) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hh := dyadic_order_tends_infinity.eventually_ge_atTop (2*b)
  filter_upwards [hh,dyadic_buffer_eventually_small G hG] with s hs hsmall
  have ha := dyadic_buffer_positive G hpos s
  linarith

end EntropyDesigns.GapTransfer
