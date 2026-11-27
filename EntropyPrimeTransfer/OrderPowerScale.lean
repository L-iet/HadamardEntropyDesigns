/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPrimeTransfer.PolynomialPrimeInput
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.PrimeTransfer
open Filter Asymptotics
open scoped Topology
noncomputable section

/-- If k/h tends to one, the full order kh is comparable to h squared. -/
theorem product_order_isTheta (k h : ℕ → ℝ) (hh : ∀ i,0<h i)
    (hr : Tendsto (fun i => k i/h i) atTop (nhds 1)) :
    (fun i => k i*h i) =Θ[atTop] (fun i => (h i)^2) := by
  have he (i : ℕ) : k i*h i/(h i)^2=k i/h i := by
    field_simp
  have ht : Tendsto (fun i => k i*h i/(h i)^2) atTop (nhds 1) := by
    simpa only [he] using hr
  exact (isTheta_of_div_tendsto_nhds_ne_zero ht (by norm_num)).symm

/-- Arbitrary signed real powers translate from seed scale to full order. -/
theorem product_order_power_scale (k h : ℕ → ℝ) (hk : ∀ i,0≤k i)
    (hh : ∀ i,0<h i) (hr : Tendsto (fun i => k i/h i) atTop (nhds 1)) (a : ℝ) :
    (fun i => (k i*h i)^a) =Θ[atTop] (fun i => (h i)^(2*a)) := by
  have ht := (product_order_isTheta k h hh hr).rpow (r:=a)
    (Eventually.of_forall (fun i => mul_nonneg (hk i) (hh i).le))
    (Eventually.of_forall (fun i => sq_nonneg (h i)))
  have he : (fun i => ((h i)^2)^a)=(fun i => (h i)^(2*a)) := by
    funext i
    exact (Real.rpow_natCast_mul (hh i).le 2 a).symm
  rw [he] at ht
  exact ht

/-- A seed-scale power quotient has the corresponding half exponent in kh. -/
theorem quotient_power_full_order (k h : ℕ → ℝ) (hk : ∀ i,0≤k i)
    (hh : ∀ i,0<h i) (hr : Tendsto (fun i => k i/h i) atTop (nhds 1)) (a b : ℝ) :
    (fun i => (h i)^a/(h i)^b)
      =Θ[atTop] (fun i => (k i*h i)^((a-b)/2)) := by
  have ht := (product_order_power_scale k h hk hh hr ((a-b)/2)).symm
  have he : (fun i => (h i)^(2*((a-b)/2)))=(fun i => (h i)^a/(h i)^b) := by
    funext i
    rw [show 2*((a-b)/2)=a-b by ring,Real.rpow_sub (hh i)]
  rw [he] at ht
  exact ht

end
end EntropyDesigns.PrimeTransfer
