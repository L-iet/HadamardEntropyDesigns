/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyExchangeableHierarchy.ShiftVectors
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
noncomputable section
open scoped BigOperators ComplexOrder

theorem signedShift_entry_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (i j a b : G) :
    (∑ t : G,∑ ε : G → Bool,signedShift t ε i j*signedShift t ε a b)=
      if (i,j)=(a,b) then (Fintype.card (G → Bool):ℝ) else 0 := by
  classical
  have hrow (t : G) : (∑ ε : G → Bool,signedShift t ε i j*signedShift t ε a b)=
      if j=i+t ∧ b=a+t then
        (if i=a then (Fintype.card (G → Bool):ℝ) else 0) else 0 := by
    by_cases hj : j=i+t <;> by_cases hb : b=a+t <;>
      simp [signedShift,hj,hb,randomSign_pair_sum]
  by_cases hia : i=a
  · subst a
    by_cases hjb : j=b
    · subst b
      have hh (t : G) : (∑ ε : G → Bool,signedShift t ε i j*signedShift t ε i j)=
          (Fintype.card (G → Bool):ℝ)*(if j=i+t then 1 else 0) := by
        rw [hrow]
        by_cases hj : j=i+t <;> simp [hj]
      simp_rw [hh]
      rw [← Finset.mul_sum,shift_indicator_sum,mul_one]
      simp
    · have hh (t : G) : (∑ ε : G → Bool,signedShift t ε i j*signedShift t ε i b)=0 := by
        rw [hrow]
        by_cases hj : j=i+t
        · have hb : b≠i+t := fun hb => hjb (hj.trans hb.symm)
          simp [hj,hb]
        · simp [hj]
      simp_rw [hh]
      simp [hjb,Prod.ext_iff]
  · have hh (t : G) : (∑ ε : G → Bool,signedShift t ε i j*signedShift t ε a b)=0 := by
      rw [hrow]
      simp [hia]
    simp_rw [hh]
    simp [hia,Prod.ext_iff]

def shiftEnsemble {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] :
    (G × (G → Bool)) → (G×G) → ℂ := fun z => shiftVector z.1 z.2

theorem shiftEnsemble_entry_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a b : G×G) :
    (∑ z : G × (G → Bool),shiftEnsemble z a*star (shiftEnsemble z b))=
      ((if a=b then (Fintype.card (G → Bool):ℝ)/(Fintype.card G:ℝ) else 0:ℝ):ℂ) := by
  classical
  simp only [shiftEnsemble,Fintype.sum_prod_type]
  simp_rw [shiftVector_pair]
  have hh : (∑ t : G,∑ ε : G → Bool,
      signedShift t ε a.1 a.2*signedShift t ε b.1 b.2/(Fintype.card G:ℝ))=
      if a=b then (Fintype.card (G → Bool):ℝ)/(Fintype.card G:ℝ) else 0 := by
    simp_rw [← Finset.sum_div]
    rw [signedShift_entry_sum]
    rcases a with ⟨i,j⟩
    rcases b with ⟨r,c⟩
    split_ifs <;> simp
  exact_mod_cast hh

theorem shiftEnsemble_one_copy {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a b : G×G) :
    uniformHierarchy (shiftEnsemble (G:=G)) 1 (fun _ => a) (fun _ => b)=
      ((if a=b then 1/(Fintype.card G:ℝ)^2 else 0:ℝ):ℂ) := by
  classical
  have hn : (Fintype.card G:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : (Fintype.card (G → Bool):ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hv (z : G × (G → Bool)) (c : G×G) :
      tensorVector 1 (shiftEnsemble z) (fun _ => c)=shiftEnsemble z c := by
    simp [tensorVector]
  simp only [uniformHierarchy,Matrix.smul_apply,Matrix.sum_apply,pureTensor,
    Matrix.vecMulVec_apply,Pi.star_apply,hv]
  rw [shiftEnsemble_entry_sum]
  have hcard : (Fintype.card (G × (G → Bool)):ℝ)=
      (Fintype.card G:ℝ)*(Fintype.card (G → Bool):ℝ) := by
    simp only [Fintype.card_prod,Nat.cast_mul]
  rw [hcard]
  by_cases hab : a=b
  · simp only [if_pos hab]
    rw [Algebra.smul_def]
    change Complex.ofReal (1/((Fintype.card G:ℝ)*(Fintype.card (G → Bool):ℝ)))*
      Complex.ofReal ((Fintype.card (G → Bool):ℝ)/(Fintype.card G:ℝ))=
        Complex.ofReal (1/(Fintype.card G:ℝ)^2)
    rw [← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    field_simp
  · simp [hab]

end
end EntropyDesigns.ExchangeableHierarchy
