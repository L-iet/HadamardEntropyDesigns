/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.WeightedSimplex
open scoped BigOperators Topology
open Filter

 theorem shifted_power_remainder_bound (T C : ℝ) (hT : 1≤T) (hC : 0≤C) (r : ℕ) :
    (T+C)^r-T^r≤(1+C)^r*T^(r-1) := by
  have hex : (T+C)^r-T^r=
      ∑ i∈Finset.range r,T^i*C^(r-i)*(r.choose i:ℝ) := by
    rw [add_pow,Finset.sum_range_succ]
    simp
  have hK : (∑ i∈Finset.range r,C^(r-i)*(r.choose i:ℝ))≤(1+C)^r := by
    have he := add_pow (1:ℝ) C r
    rw [Finset.sum_range_succ] at he
    simp only [one_pow,one_mul,Nat.sub_self,pow_zero,Nat.choose_self,Nat.cast_one,mul_one] at he
    linarith
  rw [hex]
  calc
    _≤∑ i∈Finset.range r,T^(r-1)*(C^(r-i)*(r.choose i:ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i≤r-1 := by have hh := Finset.mem_range.mp hi;omega
      have hp := pow_le_pow_right₀ hT hir
      have hc : 0≤C^(r-i)*(r.choose i:ℝ) := by positivity
      have hh := mul_le_mul_of_nonneg_right hp hc
      simpa only [mul_assoc] using hh
    _=T^(r-1)*(∑ i∈Finset.range r,C^(r-i)*(r.choose i:ℝ)) := by rw [Finset.mul_sum]
    _≤T^(r-1)*(1+C)^r := mul_le_mul_of_nonneg_left hK (by positivity)
    _=_ := by ring

 theorem relative_simplex_error_bound (f T C D : ℝ) (r : ℕ) (hr : 1≤r)
    (hT : 1≤T) (hC : 0≤C) (hD : 0<D)
    (hl : T^r/D≤f) (hu : f≤(T+C)^r/D) :
    0≤f/(T^r/D)-1 ∧ f/(T^r/D)-1≤(1+C)^r/T := by
  have ht : 0<T := lt_of_lt_of_le (by norm_num) hT
  have hp : 0<T^r := pow_pos ht _
  have he : f/(T^r/D)-1=(D*f-T^r)/T^r := by
    field_simp <;> ring
  have hlo : T^r≤f*D := (div_le_iff₀ hD).mp hl
  have hup : f*D≤(T+C)^r := (le_div_iff₀ hD).mp hu
  have hshift := shifted_power_remainder_bound T C hT hC r
  rw [he]
  constructor
  · exact div_nonneg (by nlinarith) hp.le
  · have hnum : D*f-T^r≤(1+C)^r*T^(r-1) := by nlinarith
    have hpow : T^r=T^(r-1)*T := by
      calc
        _=T^(r-1+1) := by rw [Nat.sub_add_cancel hr]
        _=_ := pow_succ T (r-1)
    calc
      _≤((1+C)^r*T^(r-1))/T^r := div_le_div_of_nonneg_right hnum hp.le
      _=(1+C)^r/T := by
        rw [hpow]
        field_simp [ht.ne',pow_ne_zero (r-1) ht.ne']

 theorem relative_simplex_error_isBigO (f : ℝ → ℝ) (r : ℕ) (hr : 1≤r)
    (C D : ℝ) (hC : 0≤C) (hD : 0<D)
    (hb : ∀ L : ℝ,0≤L → L^r/D≤f L ∧ f L≤(L+C)^r/D) :
    (fun L : ℝ => f L/(L^r/D)-1) =O[atTop] (fun L : ℝ => 1/L) := by
  apply Asymptotics.IsBigO.of_bound ((1+C)^r)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  have hh := relative_simplex_error_bound (f L) L C D r hr hL hC hD
    (hb L (by linarith)).1 (hb L (by linarith)).2
  simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1,
    abs_of_nonneg (by positivity : (0:ℝ)≤1/L),mul_one_div] using hh.2

end EntropyDesigns.WeightedSimplex
