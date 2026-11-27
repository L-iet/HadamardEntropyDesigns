/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWitness.SupportWitness
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
@[expose] public section
namespace EntropyDesigns.SupportWitness
open scoped BigOperators Matrix

def augmentedSignMatrix {d : ℕ} (y : Fin (d+1) → (Fin d → Bool)) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℤ := fun i => Fin.cons 1 (fun j => bitSign (y i j))

theorem augmentedSignMatrix_isHadamard {d : ℕ} (y : Fin (d+1) → (Fin d → Bool))
    (horth : ∀ i j,i≠j → augmentedOrthogonal (y i) (y j)) :
    Matrix.IsHadamard (augmentedSignMatrix y) := by
  have hself (i : Fin (d+1)) : (∑ j,bitSign (y i j)*bitSign (y i j))=(d : ℤ) := by
    have hs (j : Fin d) : bitSign (y i j)*bitSign (y i j)=1 := by cases y i j <;> rfl
    simp_rw [hs]
    simp
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [augmentedSignMatrix]
    · exact bitSign_sign (y i k)
  · ext i j
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      augmentedSignMatrix,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_one,one_mul,
      Matrix.smul_apply,Matrix.one_apply,Fintype.card_fin,smul_eq_mul]
    by_cases hij : i=j
    · subst j
      rw [hself]
      simp [add_comm]
    · have hh := horth i j hij
      unfold augmentedOrthogonal at hh
      simpa [hij] using hh
  · apply isRegular_iff_ne_zero.mpr
    simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one]
    omega

end EntropyDesigns.SupportWitness
