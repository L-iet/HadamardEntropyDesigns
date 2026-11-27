/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.Affine
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators Matrix

theorem general_binary_pairwise_gram {N d : ℕ} (hd : 2≤d) (hres : N%8=4)
    (rows : Fin N → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows) :
    (binaryObservationMatrix rows)ᵀ*binaryObservationMatrix rows=
      (1 : Matrix (Fin d) (Fin d) (ZMod 2))+allOnesMatrix d (ZMod 2) := by
  classical
  obtain ⟨hfirst,_⟩ := strength_two_all_moments hd rows hOA
  ext i j
  rw [binaryObservationMatrix_entry_gram]
  by_cases hij : i=j
  · subst j
    have hc : 2*hammingWeight (fun r : Fin N => rows r i)=N := by
      have hh := hammingWeight_spin_sum (fun r : Fin N => rows r i)
      have hz : (∑ r,(bitSign (rows r i) : ℝ))=0 := by exact_mod_cast hfirst i
      rw [hz,sub_zero] at hh
      exact_mod_cast hh
    have hpar : hammingWeight (fun r : Fin N => rows r i)%2=0 := by omega
    have hcast : (hammingWeight (fun r : Fin N => rows r i) : ZMod 2)=0 :=
      (ZMod.natCast_eq_natCast_iff' _ 0 2).mpr hpar
    simpa [hammingWeight,Matrix.one_apply,allOnesMatrix,show (1 : ZMod 2)+1=0 by decide] using hcast
  · have hc := hOA i j hij true true
    have hpar : (Finset.univ.filter (fun r => rows r i=true ∧ rows r j=true)).card%2=1 := by omega
    have hcast : ((Finset.univ.filter (fun r => rows r i=true ∧ rows r j=true)).card : ZMod 2)=1 :=
      (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr hpar
    simpa [Matrix.one_apply,allOnesMatrix,hij] using hcast

theorem binary_pairwise_column_sum {N d : ℕ} (hd : 2≤d) (hres : N%8=4)
    (rows : Fin N → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows) (i : Fin d) :
    (∑ r,binaryObservationMatrix rows r i)=0 := by
  have hfirst := (strength_two_all_moments hd rows hOA).1 i
  have hc : 2*hammingWeight (fun r : Fin N => rows r i)=N := by
    have hh := hammingWeight_spin_sum (fun r : Fin N => rows r i)
    have hz : (∑ r,(bitSign (rows r i) : ℝ))=0 := by exact_mod_cast hfirst
    rw [hz,sub_zero] at hh
    exact_mod_cast hh
  have hpar : hammingWeight (fun r : Fin N => rows r i)%2=0 := by omega
  have hcast : (hammingWeight (fun r : Fin N => rows r i) : ZMod 2)=0 :=
    (ZMod.natCast_eq_natCast_iff' _ 0 2).mpr hpar
  have he : (∑ r,binaryObservationMatrix rows r i)=
      (hammingWeight (fun r : Fin N => rows r i) : ZMod 2) := by
    unfold hammingWeight
    rw [Finset.card_eq_sum_ones]
    simp only [Nat.cast_sum,Nat.cast_one,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    cases h : rows r i <;> simp [binaryObservationMatrix,h]
  exact he.trans hcast

def augmentedBinaryColumns {N d : ℕ} (rows : Fin N → Fin d → Bool) :
    Option (Fin d) → (Fin N → ZMod 2) :=
  fun i r => Option.elim i 1 (fun j => binaryObservationMatrix rows r j)

theorem binary_pairwise_augmented_independent {N d : ℕ} (hd : 2≤d)
    (hres : N%8=4) (hdeven : d%2=0)
    (rows : Fin N → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows) :
    LinearIndependent (ZMod 2) (augmentedBinaryColumns rows) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let S : ZMod 2 := ∑ i : Fin d,c (some i)
  have hgram := general_binary_pairwise_gram hd hres rows hOA
  have hcol := binary_pairwise_column_sum hd hres rows hOA
  have hchar : ∀ a : ZMod 2,a+a=0 := by decide
  have hci (j : Fin d) : c (some j)=S := by
    have hz : (∑ r : Fin N,(∑ i : Option (Fin d),c i*augmentedBinaryColumns rows i r)*
        binaryObservationMatrix rows r j)=0 := by
      apply Finset.sum_eq_zero
      intro r _
      have hr := congrFun hc r
      have hr0 : (∑ i : Option (Fin d),c i*augmentedBinaryColumns rows i r)=0 := by
        simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hr
      rw [hr0,zero_mul]
    have heq : (∑ r : Fin N,(∑ i : Option (Fin d),c i*augmentedBinaryColumns rows i r)*
        binaryObservationMatrix rows r j)=
        ∑ i : Option (Fin d),c i*(∑ r : Fin N,augmentedBinaryColumns rows i r*
          binaryObservationMatrix rows r j) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [heq,Fintype.sum_option] at hz
    simp only [augmentedBinaryColumns,Option.elim_none,Option.elim_some,one_mul,hcol,
      mul_zero,zero_add] at hz
    have he (i : Fin d) : (∑ r : Fin N,binaryObservationMatrix rows r i*
        binaryObservationMatrix rows r j)=
        ((if i=j then 1 else 0) : ZMod 2)+1 := by
      have hh := congrFun (congrFun hgram i) j
      simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.add_apply,Matrix.one_apply,
        allOnesMatrix] using hh
    simp_rw [he,mul_add,Finset.sum_add_distrib] at hz
    have hs : (∑ i : Fin d,c (some i)*(if i=j then (1 : ZMod 2) else 0))=c (some j) := by
      simp
    rw [hs] at hz
    simp only [mul_one] at hz
    change c (some j)+S=0 at hz
    linear_combination hz - hchar S
  have hS : S=0 := by
    have hcD : (d : ZMod 2)=0 := (ZMod.natCast_eq_natCast_iff' d 0 2).mpr hdeven
    calc
      S=∑ i : Fin d,S := by apply Finset.sum_congr rfl; intro i _; exact hci i
      _=0 := by simp [hcD]
  have hsome (i : Fin d) : c (some i)=0 := (hci i).trans hS
  have hnone : c none=0 := by
    have hN : 0<N := by omega
    have hh := congrFun hc (⟨0,hN⟩ : Fin N)
    simpa [Fintype.sum_option,augmentedBinaryColumns,hsome] using hh
  intro i
  cases i with
  | none => exact hnone
  | some i => exact hsome i

end
end EntropyDesigns
