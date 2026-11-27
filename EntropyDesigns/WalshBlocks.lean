module

public import EntropyDesigns.TrapCliques
public import EntropyDesigns.Completion.Base

/-! # Walsh row permutations and exact two-block Hadamard completion -/

@[expose] public section
namespace EntropyDesigns

def walshSquare {s : ℕ} : Matrix (Finset (Fin s)) (Finset (Fin s)) ℝ :=
  fun R S => (walshChar S (maskSeed R) : ℝ)

def permutedWalsh {s : ℕ} (π : (Fin s → Bool) ≃ (Fin s → Bool)) (c : ℤ) :
    Matrix (Finset (Fin s)) (Finset (Fin s)) ℝ :=
  fun R S => if S = ∅ then (c : ℝ) else (walshChar S (π (maskSeed R)) : ℝ)

theorem permutedWalsh_hadamard {s : ℕ} (π : (Fin s → Bool) ≃ (Fin s → Bool))
    (c : ℤ) (hc : c = 1 ∨ c = -1) : Matrix.IsHadamard (permutedWalsh π c) := by
  classical
  apply Completion.isHadamard_mathlib
  refine ⟨?_, ?_⟩
  · intro R S
    by_cases hS : S = ∅
    · rcases hc with rfl | rfl <;> simp [permutedWalsh, hS, Completion.IsSign]
    · rcases walshChar_sign S (π (maskSeed R)) with h | h
      · left
        simpa [permutedWalsh, hS] using congrArg (fun z : ℤ => (z : ℝ)) h
      · right
        simpa [permutedWalsh, hS] using congrArg (fun z : ℤ => (z : ℝ)) h
  · ext R T
    have hcSq : (c : ℝ) * (c : ℝ) = 1 := by rcases hc with rfl | rfl <;> norm_num
    have hpoint : ∀ S : Finset (Fin s), permutedWalsh π c R S * permutedWalsh π c T S =
        (walshChar S (π (maskSeed R)) : ℝ) * (walshChar S (π (maskSeed T)) : ℝ) := by
      intro S
      by_cases hS : S = ∅ <;> simp [permutedWalsh, hS, walshChar, hcSq]
    have hiff : π (maskSeed R) = π (maskSeed T) ↔ R = T :=
      π.injective.eq_iff.trans (maskSeedEquiv s).injective.eq_iff
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [hpoint]
    rw [walshChar_real_dual_orthogonality]
    simp [Matrix.smul_apply, Matrix.one_apply, hiff]

theorem walshSquare_hadamard (s : ℕ) : Matrix.IsHadamard (@walshSquare s) := by
  have heq : permutedWalsh (Equiv.refl (Fin s → Bool)) 1 = walshSquare := by
    ext R S
    by_cases hS : S = ∅ <;> simp [permutedWalsh, walshSquare, hS, walshChar]
  rw [← heq]
  exact permutedWalsh_hadamard _ 1 (Or.inl rfl)

theorem two_block_hadamard {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A B : Matrix ι ι ℝ) (hA : Matrix.IsHadamard A) (hB : Matrix.IsHadamard B) :
    Matrix.IsHadamard (Matrix.fromBlocks A B A (-B)) := by
  classical
  have hAr : A * A.transpose = (Fintype.card ι : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.mul_conjTranspose
  have hBr : B * B.transpose = (Fintype.card ι : ℝ) • 1 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hB.mul_conjTranspose
  have hAs : ∀ i j, A i j = 1 ∨ A i j = -1 :=
    fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hA.apply_mem i j)
  have hBs : ∀ i j, B i j = 1 ∨ B i j = -1 :=
    fun i j => Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hB.apply_mem i j)
  apply Completion.isHadamard_mathlib
  refine ⟨?_, ?_⟩
  · intro i j
    rcases i with i | i <;> rcases j with j | j
    · exact hAs i j
    · exact hBs i j
    · exact hAs i j
    · change -B i j = 1 ∨ -B i j = -1
      rcases hBs i j with h | h <;> simp [h]
  · rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, hAr, hBr, add_neg_cancel]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j <;>
      simp [Matrix.fromBlocks, Matrix.smul_apply, Fintype.card_sum,
        Nat.cast_add, hij]

end EntropyDesigns
