/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyWitness.MatrixBridge
@[expose] public section
namespace EntropyDesigns.SpanningSlopes
noncomputable section
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

def normalizedRowCode (A : Matrix (Option α) (Option α) ℤ) (r : Option α) : α → Bool :=
  fun c => decide (A r (some c)= -1)

theorem normalizedRowCode_sign (A : Matrix (Option α) (Option α) ℤ)
    (hA : Matrix.IsHadamard A) (r : Option α) (c : α) :
    bitSign (normalizedRowCode A r c)=A r (some c) := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem r (some c)) with h|h <;>
    simp [normalizedRowCode,bitSign,h]

theorem normalized_hadamard_column_sum (A : Matrix (Option α) (Option α) ℤ)
    (hA : Matrix.IsHadamard A) (hcol : ∀ r,A r none=1) (c : α) :
    (∑ r : Option α,A r (some c))=0 := by
  have h := congrArg (fun M : Matrix (Option α) (Option α) ℤ => M none (some c))
    hA.conjTranspose_mul
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,Matrix.one_apply,hcol] using h

theorem normalized_hadamard_column_pair (A : Matrix (Option α) (Option α) ℤ)
    (hA : Matrix.IsHadamard A) (c d : α) (hcd : c≠d) :
    (∑ r : Option α,A r (some c)*A r (some d))=0 := by
  have h := congrArg (fun M : Matrix (Option α) (Option α) ℤ => M (some c) (some d))
    hA.conjTranspose_mul
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.smul_apply,Matrix.one_apply,hcd] using h

theorem normalizedRowCode_injective (A : Matrix (Option α) (Option α) ℤ)
    (hA : Matrix.IsHadamard A) (hcol : ∀ r,A r none=1) :
    Function.Injective (normalizedRowCode A) := by
  intro r v heq
  by_contra hne
  have hrow (j : Option α) : A r j=A v j := by
    cases j with
    | none => rw [hcol,hcol]
    | some c =>
      have h := congrArg bitSign (congrFun heq c)
      simpa only [normalizedRowCode_sign A hA] using h
  have hself := congrArg (fun M : Matrix (Option α) (Option α) ℤ => M r r)
    hA.mul_conjTranspose
  have hoff := congrArg (fun M : Matrix (Option α) (Option α) ℤ => M r v)
    hA.mul_conjTranspose
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
    Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one] at hself
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
    Matrix.smul_apply,Matrix.one_apply,hne,ite_false,smul_eq_mul,mul_zero] at hoff
  have hs : (∑ j : Option α,A r j*A v j)=∑ j : Option α,A r j*A r j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrow j]
  rw [hs,hself] at hoff
  have hpos : (0:ℤ)<Fintype.card (Option α) := by exact_mod_cast Fintype.card_pos
  omega

end
end EntropyDesigns.SpanningSlopes
