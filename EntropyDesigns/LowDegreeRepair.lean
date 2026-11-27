module

public import EntropyDesigns.FiniteFourier
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Positive degree-two Fourier correction on the actual Boolean cube -/

@[expose] public section
namespace EntropyDesigns

def lowPolynomial {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) : ℝ :=
  fourierPolynomial (fourierCoefficient w lowCharacter) lowCharacter x

noncomputable def correctionBuffer {d : ℕ} (w : (Fin d → Bool) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (lowPolynomial w)

noncomputable def coefficientBudget {d : ℕ} (w : (Fin d → Bool) → ℝ) : ℝ :=
  ∑ i : LowIndex d, |fourierCoefficient w lowCharacter i|

theorem lowPolynomial_sum_zero {d : ℕ} (w : (Fin d → Bool) → ℝ) :
    (∑ x, lowPolynomial w x) = 0 :=
  fourierPolynomial_sum_zero _ _ lowCharacter_zero

theorem correctionBuffer_dominates {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) :
    lowPolynomial w x ≤ correctionBuffer w :=
  Finset.le_sup' (lowPolynomial w) (Finset.mem_univ x)

theorem correctionBuffer_nonneg {d : ℕ} (w : (Fin d → Bool) → ℝ) :
    0 ≤ correctionBuffer w := by
  have hsum := Finset.sum_le_sum
    (fun x (_ : x ∈ (Finset.univ : Finset (Fin d → Bool))) => correctionBuffer_dominates w x)
  rw [lowPolynomial_sum_zero] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hc : (0 : ℝ) < Fintype.card (Fin d → Bool) := by simp
  nlinarith

theorem correctionBuffer_le_budget {d : ℕ} (w : (Fin d → Bool) → ℝ) :
    correctionBuffer w ≤ coefficientBudget w := by
  apply (Finset.sup'_le_iff Finset.univ_nonempty (lowPolynomial w)).2
  intro x _
  unfold lowPolynomial fourierPolynomial coefficientBudget
  apply Finset.sum_le_sum
  intro i _
  rcases walshChar_sign i.val x with h | h
  · simpa [lowCharacter,h] using le_abs_self (fourierCoefficient w lowCharacter i)
  · simpa [lowCharacter,h] using neg_le_abs (fourierCoefficient w lowCharacter i)

noncomputable def correctedLaw {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) : ℝ :=
  affineCorrection w (lowPolynomial w) ((2 : ℝ) ^ d) (correctionBuffer w) x

theorem correctedLaw_nonneg {d : ℕ} (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∀ x, 0 ≤ correctedLaw w x :=
  affineCorrection_nonneg w (lowPolynomial w) (by positivity)
    (correctionBuffer_nonneg w) hw (correctionBuffer_dominates w)

theorem correctedLaw_mass {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hmass : ∑ x, w x = 1) :
    (∑ x, correctedLaw w x) = 1 :=
  affineCorrection_mass w (lowPolynomial w) (by positivity)
    (correctionBuffer_nonneg w) (by simp) hmass (lowPolynomial_sum_zero w)

theorem correctedLaw_low_moment {d : ℕ} (w : (Fin d → Bool) → ℝ) (i : LowIndex d) :
    (∑ x, correctedLaw w x * lowCharacter i x) = 0 := by
  apply affineCorrection_moment w (lowPolynomial w) (lowCharacter i) (by positivity)
    (lowCharacter_zero i)
  exact fourierPolynomial_cross _ _ _ lowCharacter_orthogonality i

theorem correctedLaw_mean {d : ℕ} (w : (Fin d → Bool) → ℝ) (i : Fin d) :
    (∑ x, correctedLaw w x * (bitSign (x i) : ℝ)) = 0 := by
  let j : LowIndex d := ⟨{i}, by simp⟩
  simpa [j, lowCharacter, walshChar] using correctedLaw_low_moment w j

theorem correctedLaw_pair {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (i j : Fin d) (hij : i ≠ j) :
    (∑ x, correctedLaw w x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) = 0 := by
  let k : LowIndex d := ⟨{i,j}, by simp [hij]⟩
  simpa [k, lowCharacter, walshChar, hij, mul_assoc] using correctedLaw_low_moment w k

theorem correctedLaw_collision_identity {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hmass : ∑ x, w x = 1) :
    collision (correctedLaw w) =
      1 / ((2 : ℝ) ^ d) +
      (collision w - (1 + ∑ i : LowIndex d, fourierCoefficient w lowCharacter i ^ 2) /
        ((2 : ℝ) ^ d)) / (1 + correctionBuffer w) ^ 2 := by
  apply affineCorrection_collision_identity w (lowPolynomial w)
    (by positivity) (correctionBuffer_nonneg w) (by simp) hmass (lowPolynomial_sum_zero w)
  · exact fourierPolynomial_weighted w lowCharacter
  · exact fourierPolynomial_square _ _ _ lowCharacter_orthogonality

theorem correctedLaw_collision_lower {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x, 0 ≤ w x) :
    collision w / (1 + correctionBuffer w) ^ 2 ≤ collision (correctedLaw w) :=
  affineCorrection_collision_lower w (lowPolynomial w) (by positivity)
    (correctionBuffer_nonneg w) hw (correctionBuffer_dominates w)

theorem correctedLaw_variation_bound {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1) :
    (1 / 2 : ℝ) * (∑ x, |correctedLaw w x - w x|) ≤
      correctionBuffer w / (1 + correctionBuffer w) :=
  affineCorrection_variation_bound w (lowPolynomial w) (by positivity)
    (correctionBuffer_nonneg w) (by simp) hw hmass
    (lowPolynomial_sum_zero w) (correctionBuffer_dominates w)

/-- The stated explicit input window for the actual Fourier-corrected cube law. -/
theorem correctedLaw_input_window {d : ℕ} (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1)
    (hcollision : 1 / ((d : ℝ) + 4) ≤ collision w)
    (hbuffer : correctionBuffer w ≤ 1 / (2048 * ((d : ℝ) + 4) ^ 3)) :
    (0 ≤ 1 / ((d : ℝ) + 4) - collision (correctedLaw w)) ∧
    (1 / ((d : ℝ) + 4) - collision (correctedLaw w) ≤
      1 / (1024 * ((d : ℝ) + 4) ^ 4)) ∧
    ∃ H : Matrix (Fin (d + 4)) (Fin (d + 4)) ℝ, Matrix.IsHadamard H := by
  classical
  let x := fun (a : Fin d → Bool) i => bitSign (a i)
  let A := augmentedSign x
  have hx : ∀ a i, x a i = 1 ∨ x a i = -1 := fun a i => bitSign_sign (a i)
  have hA := augmentedSign_sign x hx
  have hq := correctedLaw_nonneg w hw
  have hmassq := correctedLaw_mass w hmass
  have hisoq := augmentedSign_isotropic x (correctedLaw w) hx hmassq
    (correctedLaw_mean w) (correctedLaw_pair w)
  have hN : (0 : ℝ) < (d : ℝ) + 4 := by positivity
  have hupper := correction_deficit_window hN (correctionBuffer_nonneg w) hcollision
    (correctedLaw_collision_lower w hw) hbuffer
  have hlowern := residue_frame_deficit_nonneg (by omega) hres A (correctedLaw w)
    hA hq hmassq hisoq
  have hlower : 0 ≤ 1 / ((d : ℝ) + 4) - collision (correctedLaw w) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 3 = 4 by norm_num] using hlowern
  refine ⟨hlower, hupper, ?_⟩
  have hsmalln : 1 / (((d + 1 : ℕ) : ℝ) + 3) - collision (correctedLaw w) ≤
      1 / (1024 * (((d + 1 : ℕ) : ℝ) + 3) ^ 4) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc,
      show (1 : ℝ) + 3 = 4 by norm_num] using hupper
  have hex := (small_deficit_exact_extraction (by omega) hres A (correctedLaw w)
    hA hq hmassq hisoq hsmalln).2.2
  simpa only [Nat.add_assoc, show 1 + 3 = (4 : ℕ) by omega] using hex

theorem correctedLaw_budget_input_window {d : ℕ} (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1)
    (hcollision : 1 / ((d : ℝ) + 4) ≤ collision w)
    (hbudget : coefficientBudget w ≤ 1 / (2048 * ((d : ℝ) + 4) ^ 3)) :
    ∃ H : Matrix (Fin (d + 4)) (Fin (d + 4)) ℝ, Matrix.IsHadamard H :=
  (correctedLaw_input_window hd hres w hw hmass hcollision
    ((correctionBuffer_le_budget w).trans hbudget)).2.2

end EntropyDesigns
