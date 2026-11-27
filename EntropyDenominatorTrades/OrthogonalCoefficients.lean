/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.CoefficientDenominator
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

def orthogonalCoefficient {I J : Type*} [Fintype J]
    (H : Matrix I J ℤ) (x : J → ℤ) (i : I) : ℚ :=
  ((∑ j,x j*H i j:ℤ):ℚ)/(Fintype.card J:ℚ)

theorem real_representation_dot {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (b : I → ℝ)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ)) (i : I) :
    (∑ j,(x j:ℝ)*(H i j:ℝ))=(Fintype.card J:ℝ)*b i := by
  have hg (l : I) : (∑ j,(H l j:ℝ)*(H i j:ℝ))=
      if l=i then (Fintype.card J:ℝ) else 0 := by exact_mod_cast hgram l i
  calc
    (∑ j,(x j:ℝ)*(H i j:ℝ))=(∑ j,(∑ l,b l*(H l j:ℝ))*(H i j:ℝ)) := by simp_rw [hrep]
    _=(∑ l,b l*(∑ j,(H l j:ℝ)*(H i j:ℝ))) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=(Fintype.card J:ℝ)*b i := by simp only [hg, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]; ring

theorem real_coefficient_eq_rational {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (b : I → ℝ)
    (hn : 0<Fintype.card J)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ)) (i : I) :
    b i=(orthogonalCoefficient H x i:ℝ) := by
  have hd : ((∑ j,x j*H i j:ℤ):ℝ)=(Fintype.card J:ℝ)*b i := by
    simpa only [Int.cast_sum,Int.cast_mul] using real_representation_dot H x b hgram hrep i
  have hnR : (Fintype.card J:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold orthogonalCoefficient
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  apply (eq_div_iff hnR).mpr
  simpa only [mul_comm] using hd.symm

theorem rational_expansion_of_real_representation {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I]
    (H : Matrix I J ℤ) (x : J → ℤ) (b : I → ℝ)
    (hn : 0<Fintype.card J)
    (hgram : ∀ i l,(∑ j,H i j*H l j)=if i=l then (Fintype.card J:ℤ) else 0)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ)) :
    ∀ j,(x j:ℚ)=∑ i,orthogonalCoefficient H x i*(H i j:ℚ) := by
  intro j
  have hr := hrep j
  have hb (i : I) := real_coefficient_eq_rational H x b hn hgram hrep i
  simp_rw [hb] at hr
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact hr

theorem rational_sign_coefficients_unit {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I J ℤ) (x : J → ℤ) (hn : 0<Fintype.card J)
    (hx : ∀ j,x j=1 ∨ x j= -1)
    (hrep : ∀ j,(x j:ℚ)=∑ i,orthogonalCoefficient H x i*(H i j:ℚ)) :
    (∑ i,(orthogonalCoefficient H x i)^2)=(1:ℚ) := by
  have hnQ : (Fintype.card J:ℚ)≠0 := by exact_mod_cast hn.ne'
  have hc (i : I) : (∑ j,(x j:ℚ)*(H i j:ℚ))=
      (Fintype.card J:ℚ)*orthogonalCoefficient H x i := by
    unfold orthogonalCoefficient
    push_cast
    field_simp [hnQ]
  have hs : (∑ i,orthogonalCoefficient H x i*(∑ j,(x j:ℚ)*(H i j:ℚ)))=(Fintype.card J:ℚ) := by
    calc
      (∑ i,orthogonalCoefficient H x i*(∑ j,(x j:ℚ)*(H i j:ℚ)))=
        (∑ j,(x j:ℚ)*(∑ i,orthogonalCoefficient H x i*(H i j:ℚ))) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
      _=(∑ j,(x j:ℚ)^2) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [←hrep j]
        ring
      _=(Fintype.card J:ℚ) := by
        have he (j : J) : (x j:ℚ)^2=1 := by rcases hx j with h|h <;> simp [h]
        simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have he : (∑ i,orthogonalCoefficient H x i*(∑ j,(x j:ℚ)*(H i j:ℚ)))=
      (Fintype.card J:ℚ)*(∑ i,(orthogonalCoefficient H x i)^2) := by
    simp_rw [hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  apply mul_left_cancel₀ hnQ
  simpa only [mul_one] using he.symm.trans hs

end
end EntropyDesigns.DenominatorTrades
