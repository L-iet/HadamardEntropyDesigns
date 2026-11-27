/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizeSignMatrix (K : Matrix ι ι ℤ) (i0 : ι) : Matrix ι ι ℤ :=
  fun r j => K r i0*K r j*K i0 j*K i0 i0

theorem sign_hadamard_entry_sq (K : Matrix ι ι ℤ) (hK : Matrix.IsHadamard K)
    (r j : ι) : (K r j)^2=1 := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hK.apply_mem r j) with h|h <;> simp [h]

theorem normalizeSignMatrix_row (K : Matrix ι ι ℤ) (hK : Matrix.IsHadamard K)
    (i0 j : ι) : normalizeSignMatrix K i0 i0 j=1 := by
  calc
    _=(K i0 i0)^2*(K i0 j)^2 := by unfold normalizeSignMatrix;ring
    _=1 := by rw [sign_hadamard_entry_sq K hK,sign_hadamard_entry_sq K hK];norm_num

theorem normalizeSignMatrix_column (K : Matrix ι ι ℤ) (hK : Matrix.IsHadamard K)
    (i0 r : ι) : normalizeSignMatrix K i0 r i0=1 := by
  calc
    _=(K r i0)^2*(K i0 i0)^2 := by unfold normalizeSignMatrix;ring
    _=1 := by rw [sign_hadamard_entry_sq K hK,sign_hadamard_entry_sq K hK];norm_num

theorem normalizeSignMatrix_isHadamard (K : Matrix ι ι ℤ) (hK : Matrix.IsHadamard K)
    (i0 : ι) : Matrix.IsHadamard (normalizeSignMatrix K i0) := by
  classical
  have hrow (r v : ι) :
      (∑ j,normalizeSignMatrix K i0 r j*normalizeSignMatrix K i0 v j)=
        (K r i0*K v i0)*(∑ j,K r j*K v j) := by
    have hj (j : ι) : normalizeSignMatrix K i0 r j*normalizeSignMatrix K i0 v j=
        (K r i0*K v i0)*(K r j*K v j) := by
      calc
        _=(K r i0*K v i0)*(K r j*K v j)*(K i0 j)^2*(K i0 i0)^2 := by
          unfold normalizeSignMatrix
          ring
        _=_ := by rw [sign_hadamard_entry_sq K hK,sign_hadamard_entry_sq K hK];ring
    simp only [hj,Finset.mul_sum]
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro r j
    exact mul_mem (mul_mem (mul_mem (hK.apply_mem r i0) (hK.apply_mem r j))
      (hK.apply_mem i0 j)) (hK.apply_mem i0 i0)
  · ext r v
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [hrow]
    have hbase := congrArg (fun M : Matrix ι ι ℤ => M r v) hK.mul_conjTranspose
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul] at hbase
    rw [hbase]
    by_cases hrv : r=v
    · subst v
      simp only [ite_true,mul_one]
      rw [←pow_two,sign_hadamard_entry_sq K hK]
      simp
    · simp [hrv]
  · apply isRegular_iff_ne_zero.mpr
    haveI : Nonempty ι := ⟨i0⟩
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card ι).ne'

end
end EntropyDesigns.SpanningSlopes
