/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeTransfer.PrimeBridge
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
open Filter Set Asymptotics
open scoped Topology
noncomputable section

/-- A uniform ordinary-prime gap assumption implies a uniform gap for actual
known Hadamard orders. The distribution input remains explicit. -/
theorem uniform_prime_gap_known_orders (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hmono : MonotoneOn G (Ici 0))
    (hprime : ∀ᶠ y : ℝ in atTop, ∃ p : ℕ,
      p.Prime ∧ y-G y≤(p:ℝ) ∧ (p:ℝ)≤y) :
    GapTransfer.uniformGapInput (fun x => 2*G (x/2)) := by
  have hshift : Tendsto (fun x : ℝ => x/2-1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (2*(b+1))] with x hx
    linarith
  have hsmall : ∀ᶠ y : ℝ in atTop, G y/y < 1/2 :=
    hG.tendsto_div_nhds_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have haway : ∀ᶠ y : ℝ in atTop, 2<y-G y := by
    filter_upwards [hsmall,eventually_ge_atTop (6:ℝ)] with y hy hy6
    have hg : G y<y/2 := by
      have hh := (div_lt_iff₀ (by linarith : (0:ℝ)<y)).mp hy
      linarith
    linarith
  filter_upwards [hshift.eventually hprime,hshift.eventually haway,
    eventually_gt_atTop (6:ℝ)] with x hx ha h6
  exact prime_interval_known_order G hmono x h6 ha hx

end
end EntropyDesigns.PrimeTransfer
