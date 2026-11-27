/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.OffsetBlocks
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section
open scoped BigOperators

def offsetHadamard {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) :
    Matrix (Fin k × (Fin s → Bool)) (Fin k × (Fin s → Bool)) ℤ :=
  fun r z => completedOffsetRow e i0 c (fun i j => K i j) r.1 r.2 (z.1,seedMask z.2)

theorem fullSourceRow_sign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (x : BlockSeeds k s) (z : Fin k × Finset (Fin s)) :
    fullSourceRow e i0 x z=1 ∨ fullSourceRow e i0 x z= -1 := by
  classical
  unfold fullSourceRow
  split
  · rcases walshChar_sign e (x i0) with h|h <;>
      rcases walshChar_sign e (x z.1) with h'|h' <;> simp [h,h']
  · exact walshChar_sign z.2 (x z.1)

theorem offsetHadamard_row_inner {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ)
    (hK : Matrix.IsHadamard K) (r v : Fin k × (Fin s → Bool)) :
    (∑ z,offsetHadamard e i0 c K r z*offsetHadamard e i0 c K v z)=
      if r=v then (k:ℤ)*(2:ℤ)^s else 0 := by
  classical
  have hchange (j : Fin k) :
      (∑ b : Fin s → Bool,offsetHadamard e i0 c K r (j,b)*offsetHadamard e i0 c K v (j,b))=
      ∑ S : Finset (Fin s),completedOffsetRow e i0 c (fun i j => K i j) r.1 r.2 (j,S)*
        completedOffsetRow e i0 c (fun i j => K i j) v.1 v.2 (j,S) := by
    exact Equiv.sum_comp (maskSeedEquiv s).symm
      (fun S : Finset (Fin s) => completedOffsetRow e i0 c (fun i j => K i j) r.1 r.2 (j,S)*
        completedOffsetRow e i0 c (fun i j => K i j) v.1 v.2 (j,S))
  rw [Fintype.sum_prod_type]
  simp_rw [hchange]
  rw [completedOffsetRow_inner]
  have hdot := congrArg (fun M : Matrix (Fin k) (Fin k) ℤ => M r.1 v.1) hK.mul_conjTranspose
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,Matrix.smul_apply,
    Matrix.one_apply,Fintype.card_fin,smul_eq_mul] at hdot
  rw [hdot]
  by_cases ha : r.2=v.2 <;> by_cases ht : r.1=v.1 <;>
    simp [ha,ht,Prod.ext_iff,mul_comm]

theorem offsetHadamard_isHadamard {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ)
    (hK : Matrix.IsHadamard K) : Matrix.IsHadamard (offsetHadamard e i0 c K) := by
  classical
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro r z
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    have hentry := Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hK.apply_mem r.1 z.1)
    rcases hentry with h|h <;>
      rcases fullSourceRow_sign e i0 (offsetSeed c r.2) (z.1,seedMask z.2) with h'|h' <;>
      simp [offsetHadamard,completedOffsetRow,h,h']
  · ext r v
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [offsetHadamard_row_inner e i0 c K hK]
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,Fintype.card_bool,
      Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    split <;> simp_all
  · apply isRegular_iff_ne_zero.mpr
    have hk : 0<k := by have h := i0.isLt;omega
    have hc : 0<Fintype.card (Fin k × (Fin s → Bool)) := by
      simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_fun,Fintype.card_bool]
      positivity
    exact_mod_cast hc.ne'

theorem offsetHadamard_recovers_clique {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (t0 : Fin k)
    (hfirst : ∀ j,K t0 j=1) (a : Fin s → Bool) (z : Fin k × (Fin s → Bool)) :
    offsetHadamard e i0 c K (t0,a) z=fullSourceRow e i0 (offsetSeed c a) (z.1,seedMask z.2) := by
  simp only [offsetHadamard,completedOffsetRow,hfirst,one_mul]

end
end EntropyDesigns.SupportFace
