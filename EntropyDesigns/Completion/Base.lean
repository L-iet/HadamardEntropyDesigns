/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Original proofs from the companion completion-theory project, copied locally
for an independently buildable repository; only namespace/imports adapted. -/
module
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Star
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns.Completion
open Matrix

def IsSign (x : ℝ) : Prop := x = 1 ∨ x = -1

/-- Every entry is a real sign. -/
def IsSignMatrix {ι κ : Type*} (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, IsSign (A i j)

/-- Orthogonal sign rows with their actual squared row norm. -/
def IsPartialHadamard {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix ι κ ℝ) : Prop :=
  IsSignMatrix A ∧ A * Aᵀ = (Fintype.card κ : ℝ) • (1 : Matrix ι ι ℝ)

/-- A square sign matrix with its genuine Hadamard Gram identity. -/
def IsHadamard {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop := IsPartialHadamard A

theorem isSign_sq {x : ℝ} (h : IsSign x) : x ^ 2 = 1 := by
  rcases h with rfl | rfl <;> norm_num

theorem orthogonal_row_transform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q W : Matrix ι ι ℝ) (weight : ℝ)
    (hQ : Q * Qᵀ = 1) (hW : W * Wᵀ = weight • 1) :
    (Q * W) * (Q * W)ᵀ = weight • 1 := by
  calc
    (Q * W) * (Q * W)ᵀ = Q * (W * Wᵀ) * Qᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = weight • (Q * Qᵀ) := by rw [hW]; simp
    _ = weight • 1 := by rw [hQ]

theorem isHadamard_mathlib {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : Matrix ι ι ℝ} (hA : IsHadamard A) : Matrix.IsHadamard A := by
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    exact Unitary.mem_iff_eq_one_or_eq_neg_one.mpr (hA.1 i j)
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.2
  · apply isRegular_iff_ne_zero.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)


end EntropyDesigns.Completion
