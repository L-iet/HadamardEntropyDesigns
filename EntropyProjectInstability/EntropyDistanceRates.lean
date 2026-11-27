/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.SublinearDyadic
public import Mathlib.Analysis.Real.Sqrt
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem normalized_inverse_order_ratio_one (h k : ℕ → ℝ)
    (hp : ∀ i,0<h i) (kp : ∀ i,0<k i)
    (hr : Tendsto (fun i => k i/h i) atTop (nhds 1)) :
    Tendsto (fun i => Real.sqrt (k i*h i)/k i) atTop (nhds 1) := by
  have hix := hr.inv₀ (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun i => (k i/h i)⁻¹) atTop (nhds ((1:ℝ)⁻¹)) at hix
  have hi : Tendsto (fun i => h i/k i) atTop (nhds 1) := by
    simpa only [inv_div,inv_one] using hix
  have ht := (Real.continuous_sqrt.tendsto 1).comp hi
  have he (i : ℕ) : Real.sqrt (k i*h i)/k i=Real.sqrt (h i/k i) := by
    calc
      _=Real.sqrt (k i*h i)/Real.sqrt ((k i)^2) := by rw [Real.sqrt_sq (kp i).le]
      _=Real.sqrt (k i*h i/(k i)^2) := (Real.sqrt_div (mul_pos (kp i) (hp i)).le _).symm
      _=Real.sqrt (h i/k i) := by congr 1;field_simp [(kp i).ne'] <;> ring
  simpa only [he,Function.comp_def,Real.sqrt_one] using ht

/-- The common entropy excess log(h/k) is asymptotic to 1-k/h. -/
theorem reciprocal_entropy_ratio_one (r : ℕ → ℝ)
    (hp : ∀ i,0<r i) (hlt : ∀ i,r i<1)
    (hr : Tendsto r atTop (nhds 1)) :
    Tendsto (fun i => -Real.log (r i)/(1-r i)) atTop (nhds 1) := by
  have hlo (i : ℕ) : 1≤-Real.log (r i)/(1-r i) := by
    apply (le_div_iff₀ (sub_pos.mpr (hlt i))).mpr
    have hh := Real.log_le_sub_one_of_pos (hp i)
    linarith
  have hhi (i : ℕ) : -Real.log (r i)/(1-r i)≤1/r i := by
    apply (div_le_iff₀ (sub_pos.mpr (hlt i))).mpr
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr (hp i))
    rw [Real.log_inv] at hh
    calc
      -Real.log (r i)≤(r i)⁻¹-1 := hh
      _=(1/r i)*(1-r i) := by field_simp [(hp i).ne'] <;> ring
  have hi0 := hr.inv₀ (by norm_num : (1:ℝ)≠0)
  change Tendsto (fun i => (r i)⁻¹) atTop (nhds ((1:ℝ)⁻¹)) at hi0
  have hi : Tendsto (fun i => 1/r i) atTop (nhds 1) := by simpa only [one_div,inv_one] using hi0
  have hu : Tendsto (fun i => 1/r i-1) atTop (nhds 0) := by
    simpa only [sub_self] using hi.sub (tendsto_const_nhds (x:=(1:ℝ)))
  have he : Tendsto (fun i => -Real.log (r i)/(1-r i)-1) atTop (nhds 0) :=
    squeeze_zero (fun i => by linarith [hlo i]) (fun i => by linarith [hhi i]) hu
  have ht := (tendsto_const_nhds (x:=(1:ℝ))).add he
  change Tendsto (fun i => 1+(-Real.log (r i)/(1-r i)-1)) atTop (nhds ((1:ℝ)+0)) at ht
  simp only [add_zero] at ht
  convert ht using 1
  funext i
  ring

/-- Asymptotic equality preserves a logarithmic power exponent. -/
theorem logarithmic_rate_of_ratio_one (f b n : ℕ → ℝ) (c : ℝ)
    (hf : ∀ i,0<f i) (hb : ∀ i,0<b i)
    (hn : Tendsto (fun i => Real.log (n i)) atTop atTop)
    (hr : Tendsto (fun i => f i/b i) atTop (nhds 1))
    (hc : Tendsto (fun i => Real.log (b i)/Real.log (n i)) atTop (nhds c)) :
    Tendsto (fun i => Real.log (f i)/Real.log (n i)) atTop (nhds c) := by
  have hl : Tendsto (fun i => Real.log (f i/b i)) atTop (nhds 0) := by
    simpa only [Real.log_one] using hr.log (by norm_num : (1:ℝ)≠0)
  have hz := hl.mul hn.inv_tendsto_atTop
  change Tendsto (fun i => Real.log (f i/b i)*(Real.log (n i))⁻¹) atTop (nhds (0*0)) at hz
  simp only [mul_zero] at hz
  have ht := hz.add hc
  simp only [zero_add] at ht
  convert ht using 1
  funext i
  rw [Real.log_div (hf i).ne' (hb i).ne']
  simp only [←div_eq_mul_inv]
  ring

end
end EntropyDesigns.ProjectInstability
