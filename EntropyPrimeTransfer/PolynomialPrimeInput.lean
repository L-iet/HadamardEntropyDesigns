/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeTransfer.UniformPrimeGap
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
open Filter Set Asymptotics
open scoped Topology
noncomputable section

/-- Every exponent below one gives a sublinear real power on the positive tail. -/
theorem power_gap_sublinear (θ : ℝ) (hθ : θ<1) :
    (fun x : ℝ => x^θ) =o[atTop] (fun x : ℝ => x) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    exact fun hz => False.elim (hx.ne' hz)
  · have ht := tendsto_rpow_neg_atTop (by linarith : (0:ℝ)<1-θ)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [show -(1-θ)=θ-1 by ring,Real.rpow_sub hx,Real.rpow_one]

/-- An ordinary power prime-gap assumption implies actual known-order gaps. -/
theorem power_prime_gap_known_orders (θ : ℝ) (hpos : 0<θ) (hθ : θ<1)
    (hprime : ∀ᶠ y : ℝ in atTop, ∃ p : ℕ,
      p.Prime ∧ y-y^θ≤(p:ℝ) ∧ (p:ℝ)≤y) :
    GapTransfer.uniformGapInput (fun x => 2*(x/2)^θ) := by
  apply uniform_prime_gap_known_orders _ (power_gap_sublinear θ hθ) _ hprime
  intro a ha b hb hab
  exact Real.rpow_le_rpow ha hab hpos.le

end
end EntropyDesigns.PrimeTransfer
