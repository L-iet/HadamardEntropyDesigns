/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantitative.RankLoss
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators

def signCorrelation {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (i j : Fin m) : ℤ :=
  ∑ z,(bitSign (rows z i)*bitSign (rows z j))

theorem balanced_sign_correlation_identity {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (i j : Fin m)
    (hi : (∑ z,bitSign (rows z i))=0) (hj : (∑ z,bitSign (rows z j))=0) :
    signCorrelation rows i j= -(Fintype.card ι : ℤ)+
      4*(∑ z,if rows z i=true ∧ rows z j=true then (1 : ℤ) else 0) := by
  classical
  have ht (z : ι) : bitSign (rows z i)*bitSign (rows z j)=
      (bitSign (rows z i)+bitSign (rows z j)-1)+
        4*(if rows z i=true ∧ rows z j=true then (1 : ℤ) else 0) := by
    cases hzi : rows z i <;> cases hzj : rows z j <;> norm_num [bitSign,hzi,hzj]
  unfold signCorrelation
  simp_rw [ht]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib,hi,hj,←Finset.mul_sum]
  simp

theorem balanced_sign_correlation_div_four {ι : Type*} [Fintype ι] {m : ℕ}
    (hN : Fintype.card ι%4=0) (rows : ι → Fin m → Bool) (i j : Fin m)
    (hi : (∑ z,bitSign (rows z i))=0) (hj : (∑ z,bitSign (rows z j))=0) :
    (4 : ℤ)∣signCorrelation rows i j := by
  have hn : (4 : ℤ)∣(Fintype.card ι : ℤ) := by exact_mod_cast (Nat.dvd_of_mod_eq_zero hN)
  rw [balanced_sign_correlation_identity rows i j hi hj]
  exact dvd_add (dvd_neg.mpr hn) (dvd_mul_right _ _)

theorem balanced_nonzero_correlation_square {ι : Type*} [Fintype ι] {m : ℕ}
    (hN : Fintype.card ι%4=0) (rows : ι → Fin m → Bool) (i j : Fin m)
    (hi : (∑ z,bitSign (rows z i))=0) (hj : (∑ z,bitSign (rows z j))=0)
    (hne : signCorrelation rows i j≠0) : 16≤(signCorrelation rows i j)^2 := by
  obtain ⟨k,hk⟩ := balanced_sign_correlation_div_four hN rows i j hi hj
  have hk0 : k≠0 := by intro h; apply hne; simp [hk,h]
  have hs : 1≤k^2 := by have h := sq_pos_of_ne_zero hk0; omega
  rw [hk]
  nlinarith

end EntropyDesigns
