module

public import EntropyDesigns.Entropy

/-! # Exact unbiased sign laws and their sharp entropy inequalities -/

@[expose] public section
namespace EntropyDesigns

def augmentedSign {α : Type*} {d : ℕ} (x : α → Fin d → ℤ) (a : α) :
    Fin (d + 1) → ℤ := Fin.cases 1 (x a)

theorem augmentedSign_sign {α : Type*} {d : ℕ} (x : α → Fin d → ℤ)
    (hsign : ∀ a i, x a i = 1 ∨ x a i = -1) :
    ∀ a i, augmentedSign x a i = 1 ∨ augmentedSign x a i = -1 := by
  intro a i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [augmentedSign]
  · simpa [augmentedSign] using hsign a j

theorem augmentedSign_isotropic {α : Type*} [Fintype α] {d : ℕ}
    (x : α → Fin d → ℤ) (w : α → ℝ)
    (hsign : ∀ a i, x a i = 1 ∨ x a i = -1)
    (hmass : ∑ a, w a = 1)
    (hmean : ∀ i, ∑ a, w a * (x a i : ℝ) = 0)
    (hpair : ∀ i j, i ≠ j → ∑ a, w a * (x a i : ℝ) * (x a j : ℝ) = 0) :
    ∀ i j, ∑ a, w a * (augmentedSign x a i : ℝ) * (augmentedSign x a j : ℝ) =
      if i = j then 1 else 0 := by
  have hsecond : ∀ i j, ∑ a, w a * (x a i : ℝ) * (x a j : ℝ) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · subst j
      simp only [ite_true]
      calc
        ∑ a, w a * (x a i : ℝ) * (x a i : ℝ) = ∑ a, w a := by
          apply Finset.sum_congr rfl
          intro a _
          rcases hsign a i with hx | hx <;> simp [hx]
        _ = 1 := hmass
    · simp [h, hpair i j h]
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [augmentedSign] using hmass
    · have hne : (0 : Fin (d + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simpa [augmentedSign, hne] using hmean j
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [augmentedSign] using hmean i
    · simpa [augmentedSign] using hsecond i j

/-- An integer encoding of a Boolean sign bit. -/
def bitSign (b : Bool) : ℤ := if b then -1 else 1

theorem bitSign_sign (b : Bool) : bitSign b = 1 ∨ bitSign b = -1 := by
  cases b <;> simp [bitSign]

/-- Sharp collision, collision-entropy and Shannon bounds for an actual
probability law on the d-bit cube with its exact unbiased pairwise moments.
This proves all three inequalities in the paper's residue-sensitive theorem;
the equality/completion classification is not asserted by this declaration. -/
theorem sharp_sign_cube_entropy_bounds {d : ℕ} (hd : 2 ≤ d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hmass : ∑ a, w a = 1)
    (hmean : ∀ i, ∑ a, w a * (bitSign (a i) : ℝ) = 0)
    (hpair : ∀ i j, i ≠ j →
      ∑ a, w a * (bitSign (a i) : ℝ) * (bitSign (a j) : ℝ) = 0) :
    collision w ≤ 1 / (roundedDimension (d + 1) : ℝ) ∧
      Real.log (roundedDimension (d + 1)) ≤ collisionEntropy w ∧
      Real.log (roundedDimension (d + 1)) ≤ shannon w := by
  let x := fun (a : Fin d → Bool) i => bitSign (a i)
  have hsign : ∀ a i, x a i = 1 ∨ x a i = -1 :=
    fun a i => bitSign_sign (a i)
  exact sharp_frame_entropy_bounds (by omega) (augmentedSign x) w
    (augmentedSign_sign x hsign) hw hmass
    (augmentedSign_isotropic x w hsign hmass hmean hpair)

end EntropyDesigns
