/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.OffsetHadamard
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def walshSeedMatrix (r : ℕ) : Matrix (Fin r → Bool) (Fin r → Bool) ℤ :=
  fun a b => walshChar (seedMask b) a

theorem walshSeedMatrix_isHadamard (r : ℕ) : Matrix.IsHadamard (walshSeedMatrix r) := by
  classical
  have hrow (a b : Fin r → Bool) :
      (∑ z,walshSeedMatrix r a z*walshSeedMatrix r b z)=
        if a=b then (2:ℤ)^r else 0 := by
    calc
      _ = ∑ S : Finset (Fin r),walshChar S a*walshChar S b :=
        Equiv.sum_comp (maskSeedEquiv r).symm (fun S => walshChar S a*walshChar S b)
      _ = _ := walshChar_dual_orthogonality a b
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro a b
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (walshChar_sign (seedMask b) a)
  · ext a b
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [hrow]
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
    split <;> simp_all
  · apply isRegular_iff_ne_zero.mpr
    simp

theorem normalized_walsh_exists {k : ℕ} (r : ℕ) (hk : k=2^r) (i0 : Fin k) :
    ∃ K : Matrix (Fin k) (Fin k) ℤ,Matrix.IsHadamard K ∧
      (∀ j,K i0 j=1) ∧ (∀ t,K t i0=1) := by
  classical
  let E : Fin k ≃ (Fin r → Bool) := Fintype.equivOfCardEq (by simp [hk])
  let z : Fin r → Bool := fun _ => false
  let F : Fin k ≃ (Fin r → Bool) := (Equiv.swap i0 (E.symm z)).trans E
  have hF : F i0=z := by simp [F]
  let K : Matrix (Fin k) (Fin k) ℤ := fun i j => walshSeedMatrix r (F i) (F j)
  refine ⟨K,?_,?_,?_⟩
  · exact (walshSeedMatrix_isHadamard r).reindex F.symm F.symm
  · intro j
    change walshChar (seedMask (F j)) (F i0)=1
    rw [hF]
    simp [z,walshChar,bitSign]
  · intro t
    change walshChar (seedMask (F i0)) (F t)=1
    rw [hF]
    simp [z,seedMask,walshChar]

end
end EntropyDesigns.SupportFace
