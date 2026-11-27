/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.SymmetricEntropy
noncomputable section
open MeasureTheory Set
open scoped Interval

theorem integral_affine_inv_pos (a c : ℝ) (ha : 0<a) (hc : 0<c) :
    (∫ t : ℝ in (0:ℝ)..1,(a+c*t)⁻¹)=c⁻¹*Real.log ((a+c)/a) := by
  rw [intervalIntegral.integral_comp_add_mul (f:=fun x : ℝ => x⁻¹) hc.ne' a]
  simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
  rw [integral_inv_of_pos ha (add_pos ha hc)]

theorem affine_inv_intervalIntegrable (a c : ℝ) (ha : 0<a) (hc : 0<c) :
    IntervalIntegrable (fun t : ℝ => (a+c*t)⁻¹) volume 0 1 := by
  have hcont : Continuous (fun t : ℝ => a+c*t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hh : ContinuousOn (fun t : ℝ => (a+c*t)⁻¹) (Icc 0 1) := by
    apply hcont.continuousOn.inv₀
    intro t ht
    have ht0 : 0≤t := ht.1
    have hp : 0<a+c*t := by positivity
    exact hp.ne'
  exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hh

theorem binary_entropy_quadratic_strict (p : ℝ) (hp : 0<p) (hp1 : p<1) :
    4*Real.log 2*p*(1-p)≤Real.binEntropy p := by
  have hq : 0<1-p := by linarith
  have hFI := affine_inv_intervalIntegrable p (1-p) hp hq
  have hGI := affine_inv_intervalIntegrable (1-p) p hq hp
  have hHI : IntervalIntegrable (fun t : ℝ => 4*(1+t)⁻¹) volume 0 1 := by
    simpa only [one_mul] using
      (affine_inv_intervalIntegrable (1:ℝ) 1 (by norm_num) (by norm_num)).const_mul (4:ℝ)
  have hpoint : ∀ t∈Icc (0:ℝ) 1,4*(1+t)⁻¹≤
      (p+(1-p)*t)⁻¹+((1-p)+p*t)⁻¹ := by
    intro t ht
    have ht0 : 0≤t := ht.1
    let a := p+(1-p)*t
    let b := (1-p)+p*t
    have ha : 0<a := by dsimp [a]; positivity
    have hb : 0<b := by dsimp [b]; positivity
    have hs : a+b=1+t := by dsimp [a,b]; ring
    change 4*(1+t)⁻¹≤a⁻¹+b⁻¹
    calc
      _ = 4/(a+b) := by rw [hs]; rfl
      _ ≤ (a+b)/(a*b) := (div_le_div_iff₀ (add_pos ha hb) (mul_pos ha hb)).mpr (by nlinarith [sq_nonneg (a-b)])
      _ = _ := by field_simp [ha.ne',hb.ne'] <;> ring
  have hM := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) hHI (hFI.add hGI) hpoint
  have hF : (∫ t : ℝ in (0:ℝ)..1,(p+(1-p)*t)⁻¹)=(1-p)⁻¹*(-Real.log p) := by
    rw [integral_affine_inv_pos p (1-p) hp hq]
    have hs : p+(1-p)=1 := by ring
    rw [hs]
    simp
  have hG : (∫ t : ℝ in (0:ℝ)..1,((1-p)+p*t)⁻¹)=p⁻¹*(-Real.log (1-p)) := by
    rw [integral_affine_inv_pos (1-p) p hq hp]
    have hs : (1-p)+p=1 := by ring
    rw [hs]
    simp
  have hH : (∫ t : ℝ in (0:ℝ)..1,4*(1+t)⁻¹)=4*Real.log 2 := by
    have hj : (∫ t : ℝ in (0:ℝ)..1,(1+t)⁻¹)=Real.log 2 := by
      have h := integral_affine_inv_pos (1:ℝ) 1 (by norm_num) (by norm_num)
      convert h using 1 <;> norm_num
    rw [intervalIntegral.integral_const_mul,hj]
  rw [intervalIntegral.integral_add hFI hGI,hF,hG,hH] at hM
  have hm := mul_le_mul_of_nonneg_left hM (mul_pos hp hq).le
  have hE : p*(1-p)*((1-p)⁻¹*(-Real.log p)+p⁻¹*(-Real.log (1-p)))=Real.binEntropy p := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog_def]
    field_simp [hp.ne',hq.ne']
    <;> ring
  calc
    _ = p*(1-p)*(4*Real.log 2) := by ring
    _ ≤ _ := hm
    _ = _ := hE

theorem binary_entropy_quadratic_lower (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    4*Real.log 2*p*(1-p)≤Real.binEntropy p := by
  by_cases h0 : p=0
  · subst p
    simp
  · by_cases h1 : p=1
    · subst p
      simp
    · exact binary_entropy_quadratic_strict p (lt_of_le_of_ne hp (Ne.symm h0)) (lt_of_le_of_ne hp1 h1)

end
end EntropyDesigns.SymmetricEntropy
