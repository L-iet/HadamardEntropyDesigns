/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyRelativeSequence.HadamardSeed
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns.RelativeSequence
noncomputable section

def hadamardOne : Matrix (Fin 1) (Fin 1) ℤ := !![(1:ℤ)]

theorem hadamardOne_isHadamard : Matrix.IsHadamard hadamardOne := by
  have hgram : hadamardOne * Matrix.conjTranspose hadamardOne=
      (1:ℤ) • (1 : Matrix (Fin 1) (Fin 1) ℤ) := by decide
  apply Matrix.IsHadamard.of_mul_conjTranspose
  · intro i j
    apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
    left
    fin_cases i
    fin_cases j
    rfl
  · simpa only [Fintype.card_fin,Nat.cast_one] using hgram
  · apply isRegular_iff_ne_zero.mpr
    norm_num

theorem exists_hadamard_power {m : ℕ} (H : Matrix (Fin m) (Fin m) ℤ)
    (hH : Matrix.IsHadamard H) (a : ℕ) :
    ∃ K : Matrix (Fin (m^a)) (Fin (m^a)) ℤ,Matrix.IsHadamard K := by
  induction a with
  | zero =>
    exact ⟨hadamardOne,hadamardOne_isHadamard⟩
  | succ a ih =>
    obtain ⟨A,hA⟩ := ih
    let e : (Fin (m^a) × Fin m) ≃ Fin (m^(a+1)) :=
      Fintype.equivOfCardEq (by
        simp only [Fintype.card_prod,Fintype.card_fin]
        exact (Nat.pow_succ m a).symm)
    exact ⟨Matrix.reindex e e (Matrix.kronecker A H),(hA.kronecker hH).reindex e e⟩

theorem exists_hadamard_twelve_power (a : ℕ) :
    ∃ K : Matrix (Fin (12^a)) (Fin (12^a)) ℤ,Matrix.IsHadamard K :=
  exists_hadamard_power hadamardTwelve hadamardTwelve_isHadamard a

def twelvePowerMatrix (a : ℕ) : Matrix (Fin (12^a)) (Fin (12^a)) ℤ :=
  Classical.choose (exists_hadamard_twelve_power a)

theorem twelvePowerMatrix_isHadamard (a : ℕ) : Matrix.IsHadamard (twelvePowerMatrix a) :=
  Classical.choose_spec (exists_hadamard_twelve_power a)

end
end EntropyDesigns.RelativeSequence
