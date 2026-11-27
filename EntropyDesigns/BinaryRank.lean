/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CubeIsolation
public import EntropyDesigns.ModularSeed
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns
open scoped Matrix

def binaryObservationMatrix {N d : ℕ} (rows : Fin N → Fin d → Bool) :
    Matrix (Fin N) (Fin d) (ZMod 2) := fun r i => if rows r i then 1 else 0

theorem binaryObservationMatrix_entry_gram {N d : ℕ} (rows : Fin N → Fin d → Bool) (i j : Fin d) :
    ((binaryObservationMatrix rows)ᵀ*binaryObservationMatrix rows) i j =
      ((Finset.univ.filter (fun r => rows r i=true ∧ rows r j=true)).card : ZMod 2) := by
  classical
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  have ht (r : Fin N) : binaryObservationMatrix rows r i*binaryObservationMatrix rows r j=
      if rows r i=true ∧ rows r j=true then (1 : ZMod 2) else 0 := by
    cases h1 : rows r i <;> cases h2 : rows r j <;> simp [binaryObservationMatrix,h1,h2]
  simp_rw [ht]
  simp [Finset.sum_ite,Finset.sum_const]

theorem minimal_target_binary_gram {N : ℕ} (hN : 12≤N) (hres : N%8=4)
    (rows : Fin N → Fin (N-4) → Bool) (hOA : IsBinaryStrengthTwo rows) :
    (binaryObservationMatrix rows)ᵀ*binaryObservationMatrix rows=
      (1 : Matrix (Fin (N-4)) (Fin (N-4)) (ZMod 2))+allOnesMatrix (N-4) (ZMod 2) := by
  classical
  obtain ⟨hfirst,_⟩ := strength_two_all_moments (by omega) rows hOA
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

theorem even_binary_one_plus_allOnes_square (d : ℕ) (hd : d%2=0) :
    ((1 : Matrix (Fin d) (Fin d) (ZMod 2))+allOnesMatrix d (ZMod 2))*
      ((1 : Matrix (Fin d) (Fin d) (ZMod 2))+allOnesMatrix d (ZMod 2))=1 := by
  let J := allOnesMatrix d (ZMod 2)
  have hdcast : (d : ZMod 2)=0 := (ZMod.natCast_eq_natCast_iff' d 0 2).mpr hd
  have hJ : J*J=0 := by rw [allOnesMatrix_square,hdcast,zero_smul]
  have hadd : ∀ a : ZMod 2,a+a=0 := by decide
  change (1+J)*(1+J)=1
  rw [Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,Matrix.one_mul,Matrix.mul_one,hJ,add_zero]
  simp only [Matrix.one_mul,Matrix.mul_one]
  ext i j
  have hh := hadd (J i j)
  simp only [Matrix.add_apply]
  linear_combination hh

theorem minimal_target_binary_rank {N : ℕ} (hN : 12≤N) (hres : N%8=4)
    (rows : Fin N → Fin (N-4) → Bool) (hOA : IsBinaryStrengthTwo rows) :
    (binaryObservationMatrix rows)ᵀ*binaryObservationMatrix rows=
      (1 : Matrix (Fin (N-4)) (Fin (N-4)) (ZMod 2))+allOnesMatrix (N-4) (ZMod 2) ∧
      Matrix.rank (binaryObservationMatrix rows)=N-4 := by
  have hgram := minimal_target_binary_gram hN hres rows hOA
  let G : Matrix (Fin (N-4)) (Fin (N-4)) (ZMod 2) := 1+allOnesMatrix (N-4) (ZMod 2)
  have hsq : G*G=1 := even_binary_one_plus_allOnes_square (N-4) (by omega)
  have hRG : Matrix.rank G=N-4 := by
    apply le_antisymm
    · simpa only [Fintype.card_fin] using Matrix.rank_le_card_width G
    · have hh := Matrix.rank_mul_le_left G G
      rw [hsq,Matrix.rank_one] at hh
      simpa only [Fintype.card_fin] using hh
  refine ⟨hgram,le_antisymm ?_ ?_⟩
  · simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (binaryObservationMatrix rows)
  · have hh := Matrix.rank_mul_le_right (binaryObservationMatrix rows)ᵀ (binaryObservationMatrix rows)
    rw [hgram] at hh
    rw [show Matrix.rank (1+allOnesMatrix (N-4) (ZMod 2))=N-4 from hRG] at hh
    exact hh
end EntropyDesigns
