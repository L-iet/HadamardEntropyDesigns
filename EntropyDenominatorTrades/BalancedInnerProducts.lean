/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.CoefficientDenominator
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

def positiveSignIndicator (z : ℤ) : ℤ := if z=1 then 1 else 0

theorem sign_indicator_identity {z : ℤ} (hz : z=1 ∨ z= -1) :
    z=2*positiveSignIndicator z-1 := by
  rcases hz with rfl|rfl <;> norm_num [positiveSignIndicator]

theorem sign_sum_indicator_identity {I : Type*} [Fintype I] (u : I → ℤ)
    (hu : ∀ i,u i=1 ∨ u i= -1) :
    (∑ i,u i)=2*(∑ i,positiveSignIndicator (u i))-(Fintype.card I:ℤ) := by
  calc
    (∑ i,u i)=(∑ i,(2*positiveSignIndicator (u i)-1)) :=
      Finset.sum_congr rfl (fun i _ => sign_indicator_identity (hu i))
    _=2*(∑ i,positiveSignIndicator (u i))-(Fintype.card I:ℤ) := by
      rw [Finset.sum_sub_distrib,←Finset.mul_sum]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]

theorem balanced_sign_dot_identity {I : Type*} [Fintype I]
    (u v : I → ℤ) (hu : ∀ i,u i=1 ∨ u i= -1) (hv : ∀ i,v i=1 ∨ v i= -1)
    (huz : (∑ i,u i)=0) (hvz : (∑ i,v i)=0) :
    (∑ i,u i*v i)=4*(∑ i,positiveSignIndicator (u i)*positiveSignIndicator (v i))-(Fintype.card I:ℤ) := by
  have hu' := sign_sum_indicator_identity u hu
  have hv' := sign_sum_indicator_identity v hv
  have hd : (∑ i,u i*v i)=
      4*(∑ i,positiveSignIndicator (u i)*positiveSignIndicator (v i))-
      2*(∑ i,positiveSignIndicator (u i))-2*(∑ i,positiveSignIndicator (v i))+(Fintype.card I:ℤ) := by
    calc
      (∑ i,u i*v i)=(∑ i,(4*(positiveSignIndicator (u i)*positiveSignIndicator (v i))-
        2*positiveSignIndicator (u i)-2*positiveSignIndicator (v i)+1)) := by
          apply Finset.sum_congr rfl
          intro i _
          conv_lhs => rw [sign_indicator_identity (hu i),sign_indicator_identity (hv i)]
          ring
      _=_ := by
        simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
          Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [huz] at hu'
  rw [hvz] at hv'
  linarith

theorem balanced_sign_dot_divisible_four {I : Type*} [Fintype I]
    (u v : I → ℤ) (hu : ∀ i,u i=1 ∨ u i= -1) (hv : ∀ i,v i=1 ∨ v i= -1)
    (huz : (∑ i,u i)=0) (hvz : (∑ i,v i)=0)
    (m : ℕ) (hcard : Fintype.card I=4*m) :
    (4:ℤ)∣(∑ i,u i*v i) := by
  refine ⟨(∑ i,positiveSignIndicator (u i)*positiveSignIndicator (v i))-(m:ℤ),?_⟩
  rw [balanced_sign_dot_identity u v hu hv huz hvz]
  have hc : (Fintype.card I:ℤ)=4*(m:ℤ) := by exact_mod_cast hcard
  rw [hc]
  ring

theorem balanced_inner_coefficient_clears {I : Type*} [Fintype I]
    (u v : I → ℤ) (hu : ∀ i,u i=1 ∨ u i= -1) (hv : ∀ i,v i=1 ∨ v i= -1)
    (huz : (∑ i,u i)=0) (hvz : (∑ i,v i)=0)
    (m : ℕ) (hm : 0<m) (hcard : Fintype.card I=4*m) :
    ∃ z : ℤ,(m:ℚ)*(((∑ i,u i*v i:ℤ):ℚ)/(Fintype.card I:ℚ))=(z:ℚ) := by
  obtain ⟨z,hz⟩ := balanced_sign_dot_divisible_four u v hu hv huz hvz m hcard
  refine ⟨z,?_⟩
  have hzQ : ((∑ i,u i*v i:ℤ):ℚ)=4*(z:ℚ) := by exact_mod_cast hz
  have hmQ : (m:ℚ)≠0 := by exact_mod_cast hm.ne'
  rw [hzQ,hcard]
  push_cast
  field_simp [hmQ]

end
end EntropyDesigns.DenominatorTrades
