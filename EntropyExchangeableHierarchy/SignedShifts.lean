/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyExchangeableHierarchy.SignAverages
public import Mathlib.LinearAlgebra.UnitaryGroup
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
noncomputable section
open scoped BigOperators Matrix

def signedShift {G : Type*} [AddGroup G] [DecidableEq G]
    (t : G) (ε : G → Bool) : Matrix G G ℝ :=
  fun i j => if j=i+t then randomSign ε i else 0

theorem signedShift_row_moment {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) (i a : G) :
    (∑ j,signedShift t ε i j*signedShift t ε a j)=if i=a then 1 else 0 := by
  have hpoint (j : G) : signedShift t ε i j*signedShift t ε a j=
      if j=i+t then (if i=a then 1 else 0) else 0 := by
    by_cases hji : j=i+t
    · by_cases hia : i=a
      · subst a
        simp [signedShift,hji,randomSign_mul_self]
      · have hja : j≠a+t := by
          intro hh
          exact hia (add_right_cancel (hji.symm.trans hh))
        simp [signedShift,hji,hja,hia]
    · simp [signedShift,hji]
  simp_rw [hpoint]
  simp

theorem signedShift_gram {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) : signedShift t ε * (signedShift t ε)ᵀ=1 := by
  ext i a
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using
    signedShift_row_moment t ε i a

theorem signedShift_orthogonal {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) : signedShift t ε ∈ Matrix.orthogonalGroup G ℝ :=
  (Matrix.mem_orthogonalGroup_iff G ℝ).mpr (signedShift_gram t ε)

theorem signedShift_values {G : Type*} [AddGroup G] [DecidableEq G]
    (t : G) (ε : G → Bool) (i j : G) :
    signedShift t ε i j=0 ∨ signedShift t ε i j=1 ∨ signedShift t ε i j= -1 := by
  by_cases hh : j=i+t
  · cases hi : ε i <;> simp [signedShift,hh,randomSign,hi]
  · exact Or.inl (by simp [signedShift,hh])

theorem signedShift_has_zero {G : Type*} [AddGroup G] [Nontrivial G] [DecidableEq G]
    (t : G) (ε : G → Bool) : ∃ i j : G,signedShift t ε i j=0 := by
  obtain ⟨j,hj⟩ := exists_ne t
  exact ⟨0,j,by simp [signedShift,hj]⟩

theorem signedShift_squared_norm {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) :
    (∑ a : G×G,(signedShift t ε a.1 a.2)^2)=(Fintype.card G:ℝ) := by
  simp only [Fintype.sum_prod_type,pow_two]
  simp_rw [signedShift_row_moment]
  simp

theorem shift_indicator_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (i j : G) : (∑ t : G,if j=i+t then (1:ℝ) else 0)=1 := by
  have he (t : G) : j=i+t ↔ t=j-i := by
    constructor
    · intro hh
      apply (eq_sub_iff_add_eq).mpr
      simpa only [add_comm] using hh.symm
    · intro hh
      have ht := (eq_sub_iff_add_eq).mp hh
      simpa only [add_comm] using ht.symm
  simp_rw [he]
  simp

end
end EntropyDesigns.ExchangeableHierarchy
