/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyProjectInstability.SelectedDyadicLaws
public import EntropyProjectInstability.NearSquareRates
public import EntropyProjectInstability.EntropyDistanceRates
@[expose] public section
namespace EntropyDesigns.ProjectInstability
open Filter Asymptotics
open scoped Topology
noncomputable section

def DyadicLawFamily.fullOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := F.lowOrder i*F.seedOrder i

/-- All numerical near-square rates for this SAME actual unconditional family. -/
theorem dyadic_family_numeric_rates (F : DyadicLawFamily) :
    Tendsto (fun i => Real.log ((F.fullOrder i:ℝ))) atTop atTop ∧
    Tendsto (fun i => Real.log ((F.gapOrder i:ℝ)/(F.seedOrder i:ℝ))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) ∧
    Tendsto (fun i => Real.log ((F.gapOrder i:ℝ)/((F.lowOrder i:ℝ)*(F.seedOrder i:ℝ)^2))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(3:ℝ)/2)) ∧
    Tendsto (fun i => Real.log ((F.seedOrder i:ℝ)*(F.gapOrder i:ℝ))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds ((1:ℝ)/2)) ∧
    Tendsto (fun i => Real.sqrt ((F.fullOrder i:ℝ))/(F.lowOrder i:ℝ)) atTop (nhds 1) ∧
    Tendsto (fun i => Real.log (Real.log ((F.seedOrder i:ℝ)/(F.lowOrder i:ℝ)))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) := by
  let h : ℕ → ℝ := fun i => (F.seedOrder i:ℝ)
  let k : ℕ → ℝ := fun i => (F.lowOrder i:ℝ)
  let g : ℕ → ℝ := fun i => (F.gapOrder i:ℝ)
  have hp (i : ℕ) : 0<h i := by dsimp [h,DyadicLawFamily.seedOrder];positivity
  have kp (i : ℕ) : 0<k i := by dsimp [k];exact_mod_cast (dyadic_family_orders F i).1
  have gp (i : ℕ) : 0<g i := by dsimp [g];exact_mod_cast (dyadic_family_orders F i).2.2.1
  have kh (i : ℕ) : k i<h i := by dsimp [k,h];exact_mod_cast (dyadic_family_orders F i).2.1
  have hid (i : ℕ) : h i-k i=g i := by
    have ht := dyadic_family_cast_identity F i
    change k i=h i-g i at ht
    linarith
  have hindex : Tendsto (fun i : ℕ => F.base+i) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_left i F.base) tendsto_id
  have hinf : Tendsto h atTop atTop := by
    simpa only [h,DyadicLawFamily.seedOrder,Nat.cast_pow,Nat.cast_ofNat,Function.comp_def] using
      GapTransfer.dyadic_order_tends_infinity.comp hindex
  have hl : Tendsto (fun i => Real.log (h i)) atTop atTop := by
    simpa only [Function.comp_def] using Real.tendsto_log_atTop.comp hinf
  have hr : Tendsto (fun i => k i/h i) atTop (nhds 1) := by
    simpa only [k,h,DyadicLawFamily.lowOrder,DyadicLawFamily.seedOrder,DyadicLawFamily.gapOrder,Nat.cast_pow,Nat.cast_ofNat] using F.ratio
  have gr : Tendsto (fun i => Real.log (g i)/Real.log (h i)) atTop (nhds 0) := by
    simpa only [g,h,DyadicLawFamily.seedOrder,DyadicLawFamily.gapOrder,Nat.cast_pow,Nat.cast_ofNat] using F.loggap
  have rates := near_square_logarithmic_rates h k g hp kp gp hl hr gr
  have hlogn : Tendsto (fun i => Real.log (k i*h i)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hl.eventually_ge_atTop (max b 1),rates.1.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)<2))] with i hi hn
    have hlog : (0:ℝ)<Real.log (h i) := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ((le_max_right _ _).trans hi)
    have hh := (lt_div_iff₀ hlog).mp hn
    have hb := (le_max_left b 1).trans hi
    linarith
  have htv := normalized_inverse_order_ratio_one h k hp kp hr
  have hent0 := reciprocal_entropy_ratio_one (fun i => k i/h i)
    (fun i => div_pos (kp i) (hp i)) (fun i => (div_lt_one (hp i)).mpr (kh i)) hr
  have hent : Tendsto (fun i => Real.log (h i/k i)/(g i/h i)) atTop (nhds 1) := by
    have he (i : ℕ) : -Real.log (k i/h i)/(1-k i/h i)=Real.log (h i/k i)/(g i/h i) := by
      have hd : 1-k i/h i=g i/h i := by rw [←hid i];field_simp [(hp i).ne'] <;> ring
      rw [hd,←Real.log_inv,inv_div]
    simpa only [he] using hent0
  have ep (i : ℕ) : 0<Real.log (h i/k i) :=
    Real.log_pos ((one_lt_div (kp i)).mpr (kh i))
  have herate := logarithmic_rate_of_ratio_one (fun i => Real.log (h i/k i))
    (fun i => g i/h i) (fun i => k i*h i) (-(1:ℝ)/2) ep
    (fun i => div_pos (gp i) (hp i)) hlogn hent rates.2.1
  simpa only [h,k,g,DyadicLawFamily.fullOrder,Nat.cast_mul] using
    (show Tendsto (fun i => Real.log (k i*h i)) atTop atTop ∧
      Tendsto (fun i => Real.log (g i/h i)/Real.log (k i*h i)) atTop (nhds (-(1:ℝ)/2)) ∧
      Tendsto (fun i => Real.log (g i/(k i*(h i)^2))/Real.log (k i*h i)) atTop (nhds (-(3:ℝ)/2)) ∧
      Tendsto (fun i => Real.log (h i*g i)/Real.log (k i*h i)) atTop (nhds ((1:ℝ)/2)) ∧
      Tendsto (fun i => Real.sqrt (k i*h i)/k i) atTop (nhds 1) ∧
      Tendsto (fun i => Real.log (Real.log (h i/k i))/Real.log (k i*h i)) atTop (nhds (-(1:ℝ)/2)) from
        ⟨hlogn,rates.2.1,rates.2.2.1,rates.2.2.2,htv,herate⟩)

end
end EntropyDesigns.ProjectInstability
