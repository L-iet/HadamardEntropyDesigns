/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.PrimeExponentRigidity
noncomputable section

def determinantEnvelope (d : ℕ) : ℝ := (d:ℝ)^((d:ℝ)/2)/(2:ℝ)^(d-1)

theorem determinant_envelope_below_log_threshold (p s epsilon : ℝ)
    (hp : 0<p) (hs : 0<s) (hepsilon : 0<epsilon) (hlogs : 2<Real.log s)
    (hlower : (1-epsilon/4)*s≤Real.log p)
    (d : ℕ) (hd : 1≤d) (hdegree : (d:ℝ)≤(2-epsilon)*s/Real.log s) :
    determinantEnvelope d<p := by
  have hd1 : (1:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ)<(d:ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hlogpos : 0<Real.log s := by linarith
  have hcoeff : (2-epsilon)/Real.log s≤1 :=
    (div_le_iff₀ hlogpos).mpr (by linarith)
  have hR : (2-epsilon)*s/Real.log s≤s := by
    calc
      _=((2-epsilon)/Real.log s)*s := by ring
      _≤1*s := mul_le_mul_of_nonneg_right hcoeff hs.le
      _=s := by ring
  have hds : (d:ℝ)≤s := hdegree.trans hR
  have hlogd : Real.log (d:ℝ)≤Real.log s := Real.log_le_log hdpos hds
  have hmul : (d:ℝ)*Real.log s≤(2-epsilon)*s := (le_div_iff₀ hlogpos).mp hdegree
  have hbound : (d:ℝ)/2*Real.log s≤(1-epsilon/2)*s := by nlinarith
  have hsubtract : (0:ℝ)≤((d-1:ℕ):ℝ)*Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hF : 0<determinantEnvelope d :=
    div_pos (Real.rpow_pos_of_pos hdpos _) (pow_pos (by norm_num) _)
  apply (Real.log_lt_log_iff hF hp).mp
  unfold determinantEnvelope
  rw [Real.log_div (Real.rpow_pos_of_pos hdpos _).ne' (pow_ne_zero _ (by norm_num)),
    Real.log_rpow hdpos,Real.log_pow]
  calc
    _≤(d:ℝ)/2*Real.log (d:ℝ) := sub_le_self _ hsubtract
    _≤(d:ℝ)/2*Real.log s := mul_le_mul_of_nonneg_left hlogd (by positivity)
    _≤(1-epsilon/2)*s := hbound
    _<(1-epsilon/4)*s := by nlinarith [mul_pos hepsilon hs]
    _≤Real.log p := hlower

theorem determinant_envelope_le_integer_bound (R d : ℕ) (hd : 1≤d) (hdR : d≤R) :
    determinantEnvelope d≤(((R+1)^(R+1):ℕ):ℝ) := by
  have hd1 : (1:ℝ)≤(d:ℝ) := by exact_mod_cast hd
  have hdpos : (0:ℝ)<(d:ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hden : (1:ℝ)≤2^(d-1) := one_le_pow₀ (by norm_num)
  have hdle : d≤R+1 := by omega
  have hn : d^d≤(R+1)^(R+1) :=
    (Nat.pow_le_pow_left hdle d).trans (Nat.pow_le_pow_right (by omega) hdle)
  calc
    determinantEnvelope d≤(d:ℝ)^((d:ℝ)/2) :=
      div_le_self (Real.rpow_nonneg (Nat.cast_nonneg _) _) hden
    _≤(d:ℝ)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    _=((d^d:ℕ):ℝ) := by simp only [Real.rpow_natCast,Nat.cast_pow]
    _≤_ := by exact_mod_cast hn

end
end EntropyDesigns.PrimeExponentRigidity
