/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.SignedCharacters
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

theorem hadamard_all_one_row_unique {k : ℕ} (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (t : Fin k) (ht : ∀ j,K t j=1) : t=i0 := by
  classical
  by_contra hne
  have hd := congrArg (fun M : Matrix (Fin k) (Fin k) ℤ => M t i0) hK.mul_conjTranspose
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.smul_apply,
    Matrix.one_apply,Fintype.card_fin,smul_eq_mul,hne,ite_false,mul_zero,ht,hfirst,mul_one,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hd
  have hk : 0<k := by have h := i0.isLt;omega
  have hp : (0:ℤ)<k := by exact_mod_cast hk
  omega

theorem completedOffsetRow_in_source_iff {k s : ℕ} (hs : 2≤s)
    (e : Finset (Fin s)) (i0 : Fin k) (c : BlockSeeds k s)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K)
    (hfirst : ∀ j,K i0 j=1) (t : Fin k) (a : Fin s → Bool) (x : BlockSeeds k s) :
    completedOffsetRow e i0 c (fun i j => K i j) t a=fullSourceRow e i0 x ↔
      t=i0 ∧ x=offsetSeed c a := by
  classical
  constructor
  · intro heq
    have hj (j : Fin k) : K t j=1 ∧ offsetSeed c a j=x j := by
      apply signed_nonconstant_characters_unique hs
      · exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hK.apply_mem t j)
      · intro S hS
        have h := congrFun heq (j,S)
        change K t j*fullSourceRow e i0 (offsetSeed c a) (j,S)=fullSourceRow e i0 x (j,S) at h
        simp only [fullSourceRow,hS,ite_false] at h
        exact h.symm
    refine ⟨hadamard_all_one_row_unique i0 K hK hfirst t (fun j => (hj j).1),?_⟩
    funext j
    exact (hj j).2.symm
  · rintro ⟨rfl,rfl⟩
    funext z
    simp only [completedOffsetRow,hfirst,one_mul]

theorem completedOffsetRow_constant_column {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ)
    (hcol : ∀ t,K t i0=1) (t : Fin k) (a : Fin s → Bool) :
    completedOffsetRow e i0 c (fun i j => K i j) t a (i0,∅)=1 := by
  classical
  simp only [completedOffsetRow,hcol,one_mul,fullSourceRow,ite_true]
  simpa only [pow_two] using walshChar_sq e (offsetSeed c a i0)

end
end EntropyDesigns.SupportFace
