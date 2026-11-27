/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.CoefficientDenominator
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Choose
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section

def IsSignedCoordinate {I : Type*} [DecidableEq I] (a : I → ℚ) : Prop :=
  ∃ j : I,∃ e : ℤ,(e=1 ∨ e= -1) ∧ ∀ i,a i=if i=j then (e:ℚ) else 0

theorem integer_unit_vector_classification {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℤ) (hsum : (∑ i,(z i)^2)=1) :
    ∃ j : I,(z j=1 ∨ z j= -1) ∧ ∀ i,i≠j → z i=0 := by
  classical
  have hn : ∃ j,z j≠0 := by
    by_contra hex
    have hz (i : I) : z i=0 := by
      by_contra hi
      exact hex ⟨i,hi⟩
    simp [hz] at hsum
  obtain ⟨j,hj⟩ := hn
  have hp : 0<(z j)^2 := sq_pos_of_ne_zero hj
  have hlo : 1≤(z j)^2 := by omega
  have hle : (z j)^2≤1 := by
    rw [←hsum]
    exact Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ j)
  have hjsq : (z j)^2=1 := le_antisymm hle hlo
  have hsign : z j=1 ∨ z j= -1 := by
    have hlo : -1≤z j := by nlinarith
    have hhi : z j≤1 := by nlinarith
    omega
  have he := Finset.sum_erase_add (Finset.univ : Finset I) (fun i => (z i)^2) (Finset.mem_univ j)
  rw [hsum,hjsq] at he
  have he0 : (∑ i ∈ (Finset.univ : Finset I).erase j,(z i)^2)=0 := by linarith
  refine ⟨j,hsign,?_⟩
  intro i hij
  have hi : i∈(Finset.univ : Finset I).erase j := Finset.mem_erase.mpr ⟨hij,Finset.mem_univ i⟩
  have hs := Finset.single_le_sum (fun k _ => sq_nonneg (z k)) hi
  rw [he0] at hs
  exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))

theorem denominator_one_unit_is_signed_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (hsum : (∑ i,(a i)^2)=1) (hden : coefficientDenominator a=1) :
    IsSignedCoordinate a := by
  classical
  choose z hz using (coefficient_denominator_eq_one_iff a).mp hden
  have hsq : (∑ i,(z i)^2)=(1:ℤ) := by
    exact_mod_cast (show (∑ i,(z i:ℚ)^2)=(1:ℚ) from by simpa only [hz] using hsum)
  obtain ⟨j,hj,hzero⟩ := integer_unit_vector_classification z hsq
  refine ⟨j,z j,hj,?_⟩
  intro i
  by_cases hij : i=j
  · subst i
    simpa using hz j
  · rw [hz i,hzero i hij]
    simp [hij]

theorem noncoordinate_unit_denominator_gt_one {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (hsum : (∑ i,(a i)^2)=1) (hnot : ¬IsSignedCoordinate a) :
    1<coefficientDenominator a := by
  have hp := coefficient_denominator_positive a
  have hn : coefficientDenominator a≠1 := by
    intro h
    exact hnot (denominator_one_unit_is_signed_coordinate a hsum h)
  omega

end
end EntropyDesigns.DenominatorTrades
