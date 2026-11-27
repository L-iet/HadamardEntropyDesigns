module

public import EntropyDesigns.TrapLaw
public import EntropyDesigns.FrameCapEquality

/-! # The augmented frame of an arbitrary law on the trap's observed coordinates -/

@[expose] public section
namespace EntropyDesigns

def observedFrame {s : ℕ} (x : TrapCoordinate s → Bool)
    (j : Finset (Fin s) ⊕ Finset (Fin s)) : ℝ :=
  if h : j = Sum.inl ∅ then 1 else (bitSign (x ⟨j, h⟩) : ℝ)

theorem observedFrame_sign {s : ℕ} (x : TrapCoordinate s → Bool)
    (j : Finset (Fin s) ⊕ Finset (Fin s)) : observedFrame x j = 1 ∨ observedFrame x j = -1 := by
  unfold observedFrame
  split_ifs with h
  · exact Or.inl rfl
  · rcases bitSign_sign (x ⟨j, h⟩) with hb | hb <;> simp [hb]

theorem observedFrame_trapCode {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) :
    observedFrame (trapCode e u) j = (trapRow e u j : ℝ) := by
  unfold observedFrame
  split_ifs with h
  · subst j; simp [trapRow, walshChar]
  · rw [trapCode_sign]

theorem observedFrame_isotropic {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ)
    (hmass : ∑ x, w x = 1)
    (hmean : ∀ j, ∑ x, w x * (bitSign (x j) : ℝ) = 0)
    (hpair : ∀ i j, i ≠ j → ∑ x, w x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ) = 0)
    (i j : Finset (Fin s) ⊕ Finset (Fin s)) :
    (∑ x, w x * observedFrame x i * observedFrame x j) = if i = j then 1 else 0 := by
  classical
  by_cases hi : i = Sum.inl ∅
  · subst i
    by_cases hj : j = Sum.inl ∅
    · subst j; simpa [observedFrame] using hmass
    · simpa [observedFrame, hj, Ne.symm hj] using hmean ⟨j, hj⟩
  · by_cases hj : j = Sum.inl ∅
    · subst j; simpa [observedFrame, hi] using hmean ⟨i, hi⟩
    · by_cases hij : i = j
      · subst j
        have hp : ∀ x, observedFrame x i * observedFrame x i = 1 := by
          intro x; rcases observedFrame_sign x i with h | h <;> simp [h]
        simpa only [ite_true, mul_assoc, hp, mul_one] using hmass
      · have hsub : (⟨i, hi⟩ : TrapCoordinate s) ≠ ⟨j, hj⟩ := by
          intro h; exact hij (congrArg Subtype.val h)
        simpa [observedFrame, hi, hj, hij] using hpair ⟨i, hi⟩ ⟨j, hj⟩ hsub

theorem observed_frame_card (s : ℕ) :
    Fintype.card (Finset (Fin s) ⊕ Finset (Fin s)) = 2 * 2 ^ s := by
  simp [Fintype.card_sum, two_mul]

theorem trap_coordinate_card (s : ℕ) : Fintype.card (TrapCoordinate s) = 2 * 2 ^ s - 1 := by
  classical
  change Fintype.card {j : Finset (Fin s) ⊕ Finset (Fin s) // ¬j = Sum.inl ∅} = _
  rw [Fintype.card_subtype_compl]
  simp [two_mul]

end EntropyDesigns
