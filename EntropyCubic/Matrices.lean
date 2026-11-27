/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Rows12.R0
public import EntropyCubic.Rows12.R1
public import EntropyCubic.Rows12.R2
public import EntropyCubic.Rows12.R3
public import EntropyCubic.Rows12.R4
public import EntropyCubic.Rows12.R5
public import EntropyCubic.Rows12.R6
public import EntropyCubic.Rows12.R7
public import EntropyCubic.Rows12.R8
public import EntropyCubic.Rows12.R9
public import EntropyCubic.Rows12.R10
public import EntropyCubic.Rows12.R11
public import EntropyCubic.Rows20.R0
public import EntropyCubic.Rows20.R1
public import EntropyCubic.Rows20.R2
public import EntropyCubic.Rows20.R3
public import EntropyCubic.Rows20.R4
public import EntropyCubic.Rows20.R5
public import EntropyCubic.Rows20.R6
public import EntropyCubic.Rows20.R7
public import EntropyCubic.Rows20.R8
public import EntropyCubic.Rows20.R9
public import EntropyCubic.Rows20.R10
public import EntropyCubic.Rows20.R11
public import EntropyCubic.Rows20.R12
public import EntropyCubic.Rows20.R13
public import EntropyCubic.Rows20.R14
public import EntropyCubic.Rows20.R15
public import EntropyCubic.Rows20.R16
public import EntropyCubic.Rows20.R17
public import EntropyCubic.Rows20.R18
public import EntropyCubic.Rows20.R19
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators Matrix

theorem bitHadamardSign_sign {n : ℕ} (masks : Fin n → ℕ) (i j : Fin n) :
 bitHadamardSign masks i j=1 ∨ bitHadamardSign masks i j= -1 := by
 unfold bitHadamardSign
 split_ifs <;> simp

theorem benchmarkHadamard12_rowGram : ∀ i j : Fin 12,
 (∑ k,benchmarkHadamard12 i k*benchmarkHadamard12 j k)=if i=j then (12 : ℤ) else 0 := by
 intro i j
 fin_cases i
 · exact benchmarkHadamard12_row0 j
 · exact benchmarkHadamard12_row1 j
 · exact benchmarkHadamard12_row2 j
 · exact benchmarkHadamard12_row3 j
 · exact benchmarkHadamard12_row4 j
 · exact benchmarkHadamard12_row5 j
 · exact benchmarkHadamard12_row6 j
 · exact benchmarkHadamard12_row7 j
 · exact benchmarkHadamard12_row8 j
 · exact benchmarkHadamard12_row9 j
 · exact benchmarkHadamard12_row10 j
 · exact benchmarkHadamard12_row11 j

theorem benchmarkHadamard12_hadamard : Matrix.IsHadamard benchmarkHadamard12 := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (bitHadamardSign_sign _ i j)
  · ext i j
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.smul_apply,Matrix.one_apply,Fintype.card_fin,Nat.cast_ofNat,smul_eq_mul,mul_ite,mul_one,mul_zero]
      using benchmarkHadamard12_rowGram i j
  · norm_num [isRegular_iff_ne_zero]

theorem benchmarkHadamard12_normalized : ∀ i : Fin 12,benchmarkHadamard12 i 0=1 := by
  intro i
  fin_cases i <;> norm_num [benchmarkHadamard12,bitHadamardSign,benchmarkRowMask12,Nat.testBit]

theorem benchmarkHadamard20_rowGram : ∀ i j : Fin 20,
 (∑ k,benchmarkHadamard20 i k*benchmarkHadamard20 j k)=if i=j then (20 : ℤ) else 0 := by
 intro i j
 fin_cases i
 · exact benchmarkHadamard20_row0 j
 · exact benchmarkHadamard20_row1 j
 · exact benchmarkHadamard20_row2 j
 · exact benchmarkHadamard20_row3 j
 · exact benchmarkHadamard20_row4 j
 · exact benchmarkHadamard20_row5 j
 · exact benchmarkHadamard20_row6 j
 · exact benchmarkHadamard20_row7 j
 · exact benchmarkHadamard20_row8 j
 · exact benchmarkHadamard20_row9 j
 · exact benchmarkHadamard20_row10 j
 · exact benchmarkHadamard20_row11 j
 · exact benchmarkHadamard20_row12 j
 · exact benchmarkHadamard20_row13 j
 · exact benchmarkHadamard20_row14 j
 · exact benchmarkHadamard20_row15 j
 · exact benchmarkHadamard20_row16 j
 · exact benchmarkHadamard20_row17 j
 · exact benchmarkHadamard20_row18 j
 · exact benchmarkHadamard20_row19 j

theorem benchmarkHadamard20_hadamard : Matrix.IsHadamard benchmarkHadamard20 := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (bitHadamardSign_sign _ i j)
  · ext i j
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.smul_apply,Matrix.one_apply,Fintype.card_fin,Nat.cast_ofNat,smul_eq_mul,mul_ite,mul_one,mul_zero]
      using benchmarkHadamard20_rowGram i j
  · norm_num [isRegular_iff_ne_zero]

theorem benchmarkHadamard20_normalized : ∀ i : Fin 20,benchmarkHadamard20 i 0=1 := by
  intro i
  fin_cases i <;> norm_num [benchmarkHadamard20,bitHadamardSign,benchmarkRowMask20,Nat.testBit]

end EntropyDesigns
