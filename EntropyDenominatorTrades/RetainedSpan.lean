/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDenominatorTrades.HadamardObstruction
@[expose] public section
namespace EntropyDesigns.DenominatorTrades
noncomputable section
open scoped Matrix

theorem retained_orthogonality_forces_deleted_span {J : Type*} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℤ) (hA : A.IsHadamard) (hn : 0<Fintype.card J)
    (S : Finset J) (x : J → ℤ)
    (horth : ∀ i,i∉S → (∑ j,x j*A i j)=0) :
    (fun j => (x j:ℝ)) ∈ Submodule.span ℝ (Set.range (fun i : S => fun j => (A i j:ℝ))) := by
  classical
  let H : Matrix J J ℝ := fun i j => (A i j:ℝ)
  let xr : J → ℝ := fun j => (x j:ℝ)
  let b : J → ℝ := (Fintype.card J:ℝ)⁻¹ • (H*ᵥxr)
  have hnR : (Fintype.card J:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hg : H.transpose*H=(Fintype.card J:ℝ) • 1 := by
    ext i j
    have he := congrArg (fun M : Matrix J J ℤ => M i j) hA.conjTranspose_mul
    have hi : (∑ k,A k i*A k j)=if i=j then (Fintype.card J:ℤ) else 0 := by
      simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.smul_apply,
        Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] using he
    have hr : (∑ k,(A k i:ℝ)*(A k j:ℝ))=if i=j then (Fintype.card J:ℝ) else 0 := by exact_mod_cast hi
    change (∑ k,(A k i:ℝ)*(A k j:ℝ))=(Fintype.card J:ℝ)*(if i=j then 1 else 0)
    simpa only [mul_ite,mul_one,mul_zero] using hr
  have hb : H.transpose*ᵥb=xr := by
    change H.transpose*ᵥ((Fintype.card J:ℝ)⁻¹ • (H*ᵥxr))=xr
    rw [Matrix.mulVec_smul,Matrix.mulVec_mulVec,hg,Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul]
    simp [hnR]
  have hz (i : J) (hi : i∉S) : b i=0 := by
    have he : (H*ᵥxr) i=0 := by
      change (∑ j,(A i j:ℝ)*(x j:ℝ))=0
      have hh : (∑ j,A i j*x j)=0 := by simpa only [mul_comm] using horth i hi
      exact_mod_cast hh
    simp only [b,Pi.smul_apply,smul_eq_mul,he,mul_zero]
  have hrep : (fun j => (x j:ℝ))=∑ i,b i • H i := by
    funext j
    have he := congrFun hb j
    simpa only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.sum_apply,
      Pi.smul_apply,smul_eq_mul,mul_comm] using he.symm
  rw [hrep]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i∈S
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩
  · rw [hz i hi,zero_smul]
    exact Submodule.zero_mem _

end
end EntropyDesigns.DenominatorTrades
