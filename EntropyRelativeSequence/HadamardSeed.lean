/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace EntropyDesigns.RelativeSequence

/- The classical order-twelve Paley sign matrix, generated directly from the
nonzero quadratic residues modulo eleven. All entries and the complete Gram
identity below are checked by Lean's kernel using decide, without native code. -/
def hadamardTwelve : Matrix (Fin 12) (Fin 12) ℤ := ![
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1],
  ![1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1],
  ![1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1],
  ![1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1],
  ![1, -1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1],
  ![1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, 1],
  ![1, 1, -1, -1, -1, 1, -1, -1, 1, -1, 1, 1],
  ![1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1, 1],
  ![1, 1, 1, 1, -1, -1, -1, 1, -1, -1, 1, -1],
  ![1, -1, 1, 1, 1, -1, -1, -1, 1, -1, -1, 1],
  ![1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1, -1]
]

theorem hadamardTwelve_isHadamard : Matrix.IsHadamard hadamardTwelve := by
  have hsign : ∀ i j : Fin 12,hadamardTwelve i j=1 ∨ hadamardTwelve i j= -1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> decide
  have hgram : hadamardTwelve * Matrix.conjTranspose hadamardTwelve=
      (12:ℤ) • (1 : Matrix (Fin 12) (Fin 12) ℤ) := by decide
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hsign i j)
  · simpa only [Fintype.card_fin,Nat.cast_ofNat] using hgram
  · apply isRegular_iff_ne_zero.mpr
    norm_num

end EntropyDesigns.RelativeSequence
