/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.OrthogonalCoefficients
public import EntropyDenominatorTrades.BalancedInnerProducts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

theorem represented_common_orthogonal {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I J ℤ) (x w : J → ℤ) (b : I → ℝ)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ))
    (hw : ∀ i,(∑ j,H i j*w j)=0) : (∑ j,x j*w j)=0 := by
  have hr : (∑ j,(x j:ℝ)*(w j:ℝ))=0 := by
    simp_rw [hrep,Finset.sum_mul]
    rw [Finset.sum_comm]
    have he (i : I) : (∑ j,b i*(H i j:ℝ)*(w j:ℝ))=0 := by
      calc
        _=b i*(∑ j,(H i j:ℝ)*(w j:ℝ)) := by simp only [Finset.mul_sum,mul_assoc]
        _=0 := by
          have hz : (∑ j,(H i j:ℝ)*(w j:ℝ))=0 := by exact_mod_cast hw i
          rw [hz,mul_zero]
    simp only [he,Finset.sum_const_zero]
  exact_mod_cast hr

theorem sign_product_is_sign {a b : ℤ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a*b=1 ∨ a*b= -1 := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num

theorem sign_twist_dot {J : Type*} [Fintype J] (u v w : J → ℤ)
    (hw : ∀ j,w j=1 ∨ w j= -1) :
    (∑ j,(u j*w j)*(v j*w j))=(∑ j,u j*v j) := by
  apply Finset.sum_congr rfl
  intro j _
  rcases hw j with h|h <;> simp [h]

theorem outside_row_clears_coefficients {I J : Type*} [Fintype I] [Fintype J]
    (H : Matrix I J ℤ) (x w : J → ℤ) (b : I → ℝ)
    (hH : ∀ i j,H i j=1 ∨ H i j= -1)
    (hx : ∀ j,x j=1 ∨ x j= -1) (hw : ∀ j,w j=1 ∨ w j= -1)
    (hrep : ∀ j,(x j:ℝ)=∑ i,b i*(H i j:ℝ))
    (horth : ∀ i,(∑ j,H i j*w j)=0)
    (m : ℕ) (hm : 0<m) (hcard : Fintype.card J=4*m) :
    coefficientDenominator (orthogonalCoefficient H x)∣m := by
  have hxw := represented_common_orthogonal H x w b hrep horth
  apply coefficient_denominator_dvd
  intro i
  have he := balanced_inner_coefficient_clears (fun j => x j*w j) (fun j => H i j*w j)
    (fun j => sign_product_is_sign (hx j) (hw j))
    (fun j => sign_product_is_sign (hH i j) (hw j)) hxw (horth i) m hm hcard
  simpa only [orthogonalCoefficient,sign_twist_dot x (H i) w hw] using he

end
end EntropyDesigns.DenominatorTrades
