/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
The sum-of-sign-products method follows the standard divisibility argument in
mathlib's Matrix.IsHadamard.four_dvd_card (Apache-2.0); the extra closed-row
hypothesis and the resulting divisibility by eight are proved here. -/
module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
@[expose] public section
namespace EntropyDesigns.TranslationOrbits
open scoped BigOperators

theorem closed_four_rows_force_eight_divisibility {J : Type*} [Fintype J]
    (A : Matrix (Fin 5) J ℤ)
    (hpm : ∀ i j, A i j=1 ∨ A i j= -1)
    (horth : ∀ i k, i≠k → ∑ j,A i j*A k j=0)
    (γ : ℤ) (hclosed : ∀ j,A 0 j*A 1 j*A 2 j*A 3 j=γ) :
    8 ∣ Fintype.card J := by
  classical
  have htriple (j : J) : A 0 j*A 1 j*A 2 j=γ*A 3 j := by
    obtain hd | hd := hpm 3 j
    · simpa [hd] using hclosed j
    · have hc := hclosed j
      simp only [hd] at hc ⊢
      linear_combination -hc
  have hexpand (j : J) :
      (1+A 1 j*A 0 j)*(1+A 2 j*A 0 j)*(1+A 4 j*A 0 j)=
      1+A 1 j*A 0 j+A 2 j*A 0 j+A 4 j*A 0 j+
        A 1 j*A 2 j+A 1 j*A 4 j+A 2 j*A 4 j+γ*(A 3 j*A 4 j) := by
    have ht := htriple j
    obtain ha | ha := hpm 0 j
    · simp only [ha,one_mul,mul_one] at ht ⊢
      linear_combination A 4 j * ht
    · simp only [ha,mul_neg_one,neg_mul] at ht ⊢
      linear_combination A 4 j * ht
  have hdvd (j : J) : (8:ℤ) ∣
      (1+A 1 j*A 0 j)*(1+A 2 j*A 0 j)*(1+A 4 j*A 0 j) := by
    obtain ha | ha := hpm 0 j <;> obtain hb | hb := hpm 1 j <;>
      obtain hc | hc := hpm 2 j <;> obtain hz | hz := hpm 4 j <;>
      simp [ha,hb,hc,hz]
  have hsum : (∑ j,(1+A 1 j*A 0 j)*(1+A 2 j*A 0 j)*(1+A 4 j*A 0 j))=
      (Fintype.card J:ℤ) := by
    simp_rw [hexpand]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    simp [horth 1 0 (by decide),horth 2 0 (by decide),horth 4 0 (by decide),
      horth 1 2 (by decide),horth 1 4 (by decide),horth 2 4 (by decide),
      horth 3 4 (by decide)]
  rw [←Int.ofNat_dvd,←hsum]
  exact Finset.dvd_sum fun j _ => hdvd j

end EntropyDesigns.TranslationOrbits
