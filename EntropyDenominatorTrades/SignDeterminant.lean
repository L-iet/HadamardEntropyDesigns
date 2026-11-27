/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
open Matrix
noncomputable section

theorem sign_difference_twice_half {a b : ℤ}
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a-b=2*((a-b)/2) := by
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> norm_num

/-- Subtract a fixed sign row from all other rows and divide these by two.
This gives an actual integral anchor whose determinant is the normalized
sign determinant. No nonsingularity hypothesis is needed. -/
theorem normalized_anchor_determinant {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    ∃ B : Matrix I I ℤ,A.det=(2:ℤ)^(Fintype.card I-1)*B.det := by
  let d : I → ℤ := fun i => if i=pivot then 1 else 2
  let c : I → ℤ := fun i => if i=pivot then 0 else -1
  let B : Matrix I I ℤ := fun i j =>
    if i=pivot then A i j else (A i j-A pivot j)/2
  let C : Matrix I I ℤ := fun i j => A i j+c i*A pivot j
  have hc : c pivot=0 := by simp [c]
  have hdet : C.det=A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c pivot hc (fun _ _ => rfl)
  have hC : C=Matrix.diagonal d*B := by
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases hi : i=pivot
    · subst i
      simp [C,c,d,B]
    · simp only [C,c,d,B,if_neg hi,neg_one_mul]
      exact sign_difference_twice_half (hA i j) (hA pivot j)
  have hprod : (∏ i : I,d i)=(2:ℤ)^(Fintype.card I-1) := by
    have he : (∏ i ∈ (Finset.univ : Finset I).erase pivot,d i)=
        (2:ℤ)^((Finset.univ : Finset I).erase pivot).card := by
      apply Finset.prod_eq_pow_card
      intro i hi
      have hne : i≠pivot := (Finset.mem_erase.mp hi).1
      simp [d,hne]
    have hh := Finset.prod_erase_mul (Finset.univ : Finset I) d (Finset.mem_univ pivot)
    rw [he] at hh
    simpa only [d,if_pos rfl,Finset.card_erase_of_mem (Finset.mem_univ pivot),
      Finset.card_univ,mul_one] using hh.symm
  refine ⟨B,?_⟩
  rw [←hdet,hC,Matrix.det_mul,Matrix.det_diagonal,hprod]

theorem normalized_sign_determinant_dvd {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (pivot : I)
    (hA : ∀ i j,A i j=1 ∨ A i j= -1) :
    (2:ℤ)^(Fintype.card I-1)∣A.det := by
  obtain ⟨B,hB⟩ := normalized_anchor_determinant A pivot hA
  exact ⟨B.det,hB⟩

end
end EntropyDesigns.DenominatorTrades
