/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWeightedSimplex.IntegralFloorBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators
open Set MeasureTheory

 theorem integral_decreasing_affine_power (L c a b : ℝ) (hc : c≠0) (k : ℕ) :
    (∫ x in a..b,(L-c*x)^k)=
      ((L-c*a)^(k+1)-(L-c*b)^(k+1))/(c*((k:ℝ)+1)) := by
  have he : (fun x : ℝ => (L-c*x)^k)=(fun x : ℝ => ((-c)*x+L)^k) := by
    funext x
    congr 1
    ring
  rw [he,intervalIntegral.integral_comp_mul_add (fun x : ℝ => x^k) (neg_ne_zero.mpr hc) L,
    integral_pow]
  simp only [smul_eq_mul]
  have hk : (k:ℝ)+1≠0 := by positivity
  field_simp [hc,hk]
  ring

 theorem decreasing_affine_power_antitone (L c a b : ℝ) (hc : 0<c) (hb : b≤L/c) (k : ℕ) :
    AntitoneOn (fun x : ℝ => (L-c*x)^k) (Icc a b) := by
  intro x hx y hy hxy
  have hy' : y*c≤L := (le_div_iff₀ hc).mp (hy.2.trans hb)
  apply pow_le_pow_left₀ (by nlinarith : (0:ℝ)≤L-c*y)
  nlinarith

 theorem decreasing_power_floor_sum_lower (L c : ℝ) (hL : 0≤L) (hc : 0<c) (k : ℕ) :
    L^(k+1)/(c*((k:ℝ)+1))≤
      ∑ a∈Finset.range (⌊L/c⌋₊+1),(L-c*(a:ℝ))^k := by
  have hu : 0≤L/c := div_nonneg hL hc.le
  have hfloor := Nat.floor_le hu
  have hn : 0≤(L-c*(⌊L/c⌋₊:ℝ))^k := by
    apply pow_nonneg
    have hh := (le_div_iff₀ hc).mp hfloor
    nlinarith
  have hcont : Continuous (fun x : ℝ => (L-c*x)^k) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).pow k
  have hh := antitone_integral_le_floor_sum _ hcont (L/c) hu
    (decreasing_affine_power_antitone L c 0 (L/c) hc le_rfl k) hn
  have hend : L-c*(L/c)=0 := by field_simp [hc.ne'];ring
  rw [integral_decreasing_affine_power L c 0 (L/c) hc.ne' k] at hh
  simpa only [hend,mul_zero,sub_zero,zero_pow (by omega : k+1≠0)] using hh

 theorem decreasing_power_floor_sum_upper (L C c : ℝ) (hL : 0≤L) (hC : 0≤C)
    (hc : 0<c) (k : ℕ) :
    (∑ a∈Finset.range (⌊L/c⌋₊+1),(L+C-c*(a:ℝ))^k)≤
      (L+C+c)^(k+1)/(c*((k:ℝ)+1)) := by
  have hf := Nat.floor_le (div_nonneg hL hc.le)
  have hbound : (⌊L/c⌋₊:ℝ)≤(L+C)/c :=
    hf.trans (div_le_div_of_nonneg_right (by linarith) hc.le)
  have ha := decreasing_affine_power_antitone (L+C) c (-1) (⌊L/c⌋₊:ℝ) hc hbound k
  have hh := antitone_floor_sum_le_integral _ ⌊L/c⌋₊ ha
  have hbase : 0≤L+C-c*(⌊L/c⌋₊:ℝ) := by
    have hb := (le_div_iff₀ hc).mp hbound
    nlinarith
  have hstart : L+C-c*(-1)=L+C+c := by ring
  have hden : 0<c*((k:ℝ)+1) := mul_pos hc (by positivity)
  calc
    _≤∫ x in (-1:ℝ)..(⌊L/c⌋₊:ℝ),(L+C-c*x)^k := hh
    _=((L+C+c)^(k+1)-(L+C-c*(⌊L/c⌋₊:ℝ))^(k+1))/(c*((k:ℝ)+1)) := by
      rw [integral_decreasing_affine_power (L+C) c (-1) _ hc.ne' k,hstart]
    _≤_ := div_le_div_of_nonneg_right (sub_le_self _ (pow_nonneg hbase _)) hden.le

end EntropyDesigns.WeightedSimplex
