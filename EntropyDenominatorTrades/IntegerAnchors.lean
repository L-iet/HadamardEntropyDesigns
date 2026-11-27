/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.CoefficientDenominator
public import EntropyDenominatorTrades.SharpDeterminant
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Nat.Prime.Basic
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
open Matrix
open scoped Matrix
noncomputable section

theorem rational_denominator_dvd_int_multiple (x : ℚ) (D : ℤ)
    (h : ∃ z : ℤ,(D:ℚ)*x=(z:ℚ)) : (x.den:ℤ)∣D := by
  by_cases hD : D=0
  · simp [hD]
  obtain ⟨z,hz⟩ := h
  have hDQ : (D:ℚ)≠0 := by exact_mod_cast hD
  have he : x=Rat.divInt z D := by
    rw [Rat.divInt_eq_div]
    apply (eq_div_iff hDQ).mpr
    simpa only [mul_comm] using hz
  rw [he]
  exact Rat.den_dvd z D

theorem coefficient_denominator_int_dvd {I : Type*} [Fintype I]
    (a : I → ℚ) (D : ℤ) (h : ∀ i,∃ z : ℤ,(D:ℚ)*a i=(z:ℚ)) :
    (coefficientDenominator a:ℤ)∣D := by
  apply Int.natCast_dvd.mpr
  apply Finset.lcm_dvd_iff.mpr
  intro i _
  exact Int.natCast_dvd.mp (rational_denominator_dvd_int_multiple (a i) D (h i))

/-- The actual integer adjugate gives a clearing witness for every coefficient.
The matrix need not be invertible: in the singular case this still proves
the harmless, but exact, divisibility by its zero determinant. -/
theorem integer_anchor_clears_coefficients {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ)) (i : I) :
    ∃ z : ℤ,(S.det:ℚ)*a i=(z:ℚ) := by
  let f := Int.castRingHom ℚ
  let R : Matrix I I ℚ := f.mapMatrix S
  change R*ᵥa=f∘x at h
  have hd : R.det=(S.det:ℚ) := (f.map_det S).symm
  have ha : R.adjugate*ᵥ(R*ᵥa)=R.det • a := by
    rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
  rw [h] at ha
  have he : R.det*a i=(R.adjugate*ᵥ(f∘x)) i := by
    simpa only [Pi.smul_apply,smul_eq_mul] using (congrArg (fun v => v i) ha).symm
  have hm := f.map_mulVec S.adjugate x i
  change ((S.adjugate*ᵥx) i:ℚ)=(f.mapMatrix S.adjugate*ᵥ(f∘x)) i at hm
  rw [f.map_adjugate S] at hm
  refine ⟨(S.adjugate*ᵥx) i,?_⟩
  rw [←hd]
  exact he.trans hm.symm

theorem integer_anchor_denominator_divides {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ)) :
    (coefficientDenominator a:ℤ)∣S.det :=
  coefficient_denominator_int_dvd a S.det (integer_anchor_clears_coefficients S a x h)

theorem odd_denominator_divides_normalized_anchor {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (pivot : I) (hS : ∀ i j,S i j=1 ∨ S i j= -1)
    (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ))
    (hq : Odd (coefficientDenominator a)) :
    (coefficientDenominator a:ℤ)∣S.det/(2:ℤ)^(Fintype.card I-1) := by
  obtain ⟨B,hB⟩ := normalized_anchor_determinant S pivot hS
  have hd := integer_anchor_denominator_divides S a x h
  rw [hB] at hd
  have hn := Int.natCast_dvd.mp hd
  simp only [Int.natAbs_mul,Int.natAbs_pow] at hn
  norm_num at hn
  have hc : Nat.Coprime (coefficientDenominator a) (2^(Fintype.card I-1)) :=
    hq.coprime_two_right.pow_right _
  have hb : (coefficientDenominator a:ℤ)∣B.det :=
    Int.natCast_dvd.mpr (hc.dvd_of_dvd_mul_left hn)
  rw [hB,Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num : (2:ℤ)≠0))]
  exact hb

theorem odd_anchor_denominator_bound {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix I I ℤ) (pivot : I) (hS : ∀ i j,S i j=1 ∨ S i j= -1)
    (a : I → ℚ) (x : I → ℤ)
    (h : (fun i j => (S i j:ℚ))*ᵥa=fun i => (x i:ℚ))
    (hq : Odd (coefficientDenominator a)) (hdet : S.det≠0) :
    (coefficientDenominator a:ℝ)≤
      (Fintype.card I:ℝ)^((Fintype.card I:ℝ)/2)/(2:ℝ)^(Fintype.card I-1) := by
  obtain ⟨z,hz,hbound⟩ := normalized_integer_anchor_bound S pivot hS
  have hz0 : z≠0 := by intro hzero;rw [hzero,mul_zero] at hz;exact hdet hz
  have hd := odd_denominator_divides_normalized_anchor S pivot hS a x h hq
  rw [hz,Int.mul_ediv_cancel_left _ (pow_ne_zero _ (by norm_num : (2:ℤ)≠0))] at hd
  have hn := Int.natAbs_le_of_dvd_ne_zero hd hz0
  simp only [Int.natAbs_natCast] at hn
  have hnZ : (coefficientDenominator a:ℤ)≤|z| := by
    rw [←Int.natCast_natAbs z]
    exact_mod_cast hn
  have hr : (coefficientDenominator a:ℝ)≤|(z:ℝ)| := by exact_mod_cast hnZ
  exact hr.trans hbound

end
end EntropyDesigns.DenominatorTrades
