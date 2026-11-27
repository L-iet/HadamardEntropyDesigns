/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

def coefficientDenominator {I : Type*} [Fintype I] (a : I → ℚ) : ℕ :=
  Finset.univ.lcm (fun i => (a i).den)

theorem coefficient_denominator_positive {I : Type*} [Fintype I] (a : I → ℚ) :
    0<coefficientDenominator a := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun i _ => (a i).den_nz)

theorem rational_denominator_dvd_integer_multiple (x : ℚ) (D : ℕ)
    (h : ∃ z : ℤ,(D:ℚ)*x=(z:ℚ)) : x.den∣D := by
  by_cases hD : D=0
  · simp [hD]
  obtain ⟨z,hz⟩ := h
  have hDQ : (D:ℚ)≠0 := by exact_mod_cast hD
  have he : x=Rat.divInt z (D:ℤ) := by
    rw [Rat.divInt_eq_div,Int.cast_natCast]
    apply (eq_div_iff hDQ).mpr
    simpa only [mul_comm] using hz
  have hd : (x.den:ℤ)∣(D:ℤ) := by rw [he];exact Rat.den_dvd z (D:ℤ)
  exact_mod_cast hd

theorem coefficient_denominator_dvd {I : Type*} [Fintype I]
    (a : I → ℚ) (D : ℕ) (h : ∀ i,∃ z : ℤ,(D:ℚ)*a i=(z:ℚ)) :
    coefficientDenominator a∣D := by
  apply Finset.lcm_dvd_iff.mpr
  intro i _
  exact rational_denominator_dvd_integer_multiple (a i) D (h i)

theorem coefficient_denominator_clears {I : Type*} [Fintype I]
    (a : I → ℚ) (i : I) :
    ∃ z : ℤ,(coefficientDenominator a:ℚ)*a i=(z:ℚ) := by
  have hd : (a i).den∣coefficientDenominator a :=
    Finset.dvd_lcm (Finset.mem_univ i)
  obtain ⟨m,hm⟩ := hd
  refine ⟨(m:ℤ)*(a i).num,?_⟩
  calc
    (coefficientDenominator a:ℚ)*a i=((a i).den:ℚ)*(m:ℚ)*a i := by rw [hm,Nat.cast_mul]
    _=(m:ℚ)*(((a i).den:ℚ)*a i) := by ring
    _=(m:ℚ)*((a i).num:ℚ) := by rw [Rat.den_mul_eq_num]
    _=(((m:ℤ)*(a i).num:ℤ):ℚ) := by simp only [Int.cast_mul,Int.cast_natCast]

theorem coefficient_denominator_eq_one_iff {I : Type*} [Fintype I]
    (a : I → ℚ) :
    coefficientDenominator a=1 ↔ ∀ i,∃ z : ℤ,a i=(z:ℚ) := by
  constructor
  · intro h i
    obtain ⟨z,hz⟩ := coefficient_denominator_clears a i
    refine ⟨z,?_⟩
    simpa only [h,Nat.cast_one,one_mul] using hz
  · intro h
    apply Nat.dvd_one.mp
    apply coefficient_denominator_dvd a 1
    intro i
    obtain ⟨z,hz⟩ := h i
    exact ⟨z,by simpa only [Nat.cast_one,one_mul] using hz⟩

end
end EntropyDesigns.DenominatorTrades
