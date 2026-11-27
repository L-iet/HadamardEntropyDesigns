/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.SublinearDyadic
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics
open scoped Topology
noncomputable section

/-- Logarithmic exponents for the four exact near-square identities.
The assumptions concern actual positive numerical scales and their limits. -/
theorem near_square_logarithmic_rates (h k g : ℕ → ℝ)
    (hp : ∀ i,0<h i) (kp : ∀ i,0<k i) (gp : ∀ i,0<g i)
    (hl : Tendsto (fun i => Real.log (h i)) atTop atTop)
    (kr : Tendsto (fun i => k i/h i) atTop (nhds 1))
    (gr : Tendsto (fun i => Real.log (g i)/Real.log (h i)) atTop (nhds 0)) :
    Tendsto (fun i => Real.log (k i*h i)/Real.log (h i)) atTop (nhds 2) ∧
    Tendsto (fun i => Real.log (g i/h i)/Real.log (k i*h i)) atTop (nhds (-(1:ℝ)/2)) ∧
    Tendsto (fun i => Real.log (g i/(k i*(h i)^2)) / Real.log (k i*h i)) atTop (nhds (-(3:ℝ)/2)) ∧
    Tendsto (fun i => Real.log (h i*g i)/Real.log (k i*h i)) atTop (nhds ((1:ℝ)/2)) := by
  have hcl : Tendsto (fun i => Real.log (k i/h i)) atTop (nhds 0) := by
    simpa only [Real.log_one] using kr.log (by norm_num : (1:ℝ)≠0)
  have herr : Tendsto (fun i => Real.log (k i/h i)/Real.log (h i)) atTop (nhds 0) := by
    have ht := hcl.mul hl.inv_tendsto_atTop
    change Tendsto (fun i => Real.log (k i/h i)*(Real.log (h i))⁻¹) atTop (nhds (0*0)) at ht
    simpa only [div_eq_mul_inv,mul_zero] using ht
  have hnl : Tendsto (fun i => Real.log (k i*h i)/Real.log (h i)) atTop (nhds 2) := by
    have ht := (tendsto_const_nhds (x:=(2:ℝ))).add herr
    change Tendsto (fun i => (2:ℝ)+Real.log (k i/h i)/Real.log (h i)) atTop (nhds (2+0)) at ht
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [hl.eventually_ge_atTop 1] with i hi
    have hne : Real.log (h i)≠0 := by linarith
    rw [Real.log_mul (kp i).ne' (hp i).ne',Real.log_div (kp i).ne' (hp i).ne']
    field_simp <;> ring
  have hkn : Tendsto (fun i => Real.log (k i)/Real.log (h i)) atTop (nhds 1) := by
    have ht := (tendsto_const_nhds (x:=(1:ℝ))).add herr
    change Tendsto (fun i => (1:ℝ)+Real.log (k i/h i)/Real.log (h i)) atTop (nhds (1+0)) at ht
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [hl.eventually_ge_atTop 1] with i hi
    have hne : Real.log (h i)≠0 := by linarith
    rw [Real.log_div (kp i).ne' (hp i).ne']
    field_simp <;> ring
  have hgood : ∀ᶠ i : ℕ in atTop, Real.log (h i)≠0 ∧ Real.log (k i*h i)≠0 := by
    filter_upwards [hl.eventually_ge_atTop 1,hnl.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)<2))] with i hi hn
    have hnpos : 0<Real.log (k i*h i) := by
      have he := (lt_div_iff₀ (by linarith : 0<Real.log (h i))).mp hn
      linarith
    exact ⟨by linarith,hnpos.ne'⟩
  simp only [neg_div]
  refine ⟨hnl,?_,?_,?_⟩
  · have ht := (gr.sub (tendsto_const_nhds (x:=(1:ℝ)))).div hnl (by norm_num : (2:ℝ)≠0)
    change Tendsto (fun i => (Real.log (g i)/Real.log (h i)-1)/(Real.log (k i*h i)/Real.log (h i))) atTop (nhds ((0-1)/2)) at ht
    norm_num only [zero_sub] at ht
    apply ht.congr'
    filter_upwards [hgood] with i hi
    rw [Real.log_div (gp i).ne' (hp i).ne']
    field_simp [hi.1,hi.2] <;> ring
  · have ht := ((gr.sub hkn).sub (tendsto_const_nhds (x:=(2:ℝ)))).div hnl (by norm_num : (2:ℝ)≠0)
    change Tendsto (fun i => ((Real.log (g i)/Real.log (h i)-Real.log (k i)/Real.log (h i))-2)/(Real.log (k i*h i)/Real.log (h i))) atTop (nhds (((0-1)-2)/2)) at ht
    norm_num only [zero_sub,neg_sub] at ht
    apply ht.congr'
    filter_upwards [hgood] with i hi
    rw [Real.log_div (gp i).ne' (mul_pos (kp i) (sq_pos_of_pos (hp i))).ne',Real.log_mul (kp i).ne' (sq_pos_of_pos (hp i)).ne',Real.log_pow]
    field_simp [hi.1,hi.2] <;> ring
  · have ht := ((tendsto_const_nhds (x:=(1:ℝ))).add gr).div hnl (by norm_num : (2:ℝ)≠0)
    change Tendsto (fun i => (1+Real.log (g i)/Real.log (h i))/(Real.log (k i*h i)/Real.log (h i))) atTop (nhds ((1+0)/2)) at ht
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [hgood] with i hi
    rw [Real.log_mul (hp i).ne' (gp i).ne']
    field_simp [hi.1,hi.2] <;> ring

end
end EntropyDesigns.ProjectInstability
