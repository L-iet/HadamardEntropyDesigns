module

public import EntropyDesigns.SignLaws
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset

/-! # Boolean-cube characters and their exact finite orthogonality -/

@[expose] public section
namespace EntropyDesigns

def walshChar {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) : ℤ :=
  ∏ i ∈ S, bitSign (x i)

theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> simp [bitSign]

def flipCoordinate {d : ℕ} (j : Fin d) : (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun x := Function.update x j (!x j)
  invFun x := Function.update x j (!x j)
  left_inv x := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [Function.update_of_ne h]
  right_inv x := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [Function.update_of_ne h]

theorem walshChar_flip {d : ℕ} (S : Finset (Fin d)) (j : Fin d) (hj : j ∈ S)
    (x : Fin d → Bool) :
    walshChar S (flipCoordinate j x) = -walshChar S x := by
  have hrest : (∏ i ∈ S.erase j, bitSign ((flipCoordinate j x) i)) =
      ∏ i ∈ S.erase j, bitSign (x i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    simp [flipCoordinate, Function.update_of_ne hne]
  unfold walshChar
  rw [← Finset.mul_prod_erase S (fun i => bitSign ((flipCoordinate j x) i)) hj,
    ← Finset.mul_prod_erase S (fun i => bitSign (x i)) hj, hrest]
  simp [flipCoordinate, bitSign_not]

theorem walshChar_sum_zero {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    (∑ x : Fin d → Bool, walshChar S x) = 0 := by
  obtain ⟨j, hj⟩ := hS
  have he : (∑ x : Fin d → Bool, walshChar S (flipCoordinate j x)) =
      ∑ x : Fin d → Bool, walshChar S x :=
    Equiv.sum_comp (flipCoordinate j) (walshChar S)
  simp_rw [walshChar_flip S j hj] at he
  rw [Finset.sum_neg_distrib] at he
  omega

theorem walshChar_flip_of_not_mem {d : ℕ} (S : Finset (Fin d)) (j : Fin d)
    (hj : j ∉ S) (x : Fin d → Bool) :
    walshChar S (flipCoordinate j x) = walshChar S x := by
  unfold walshChar
  apply Finset.prod_congr rfl
  intro i hi
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  simp [flipCoordinate, Function.update_of_ne hne]

theorem walshChar_sign {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) :
    walshChar S x = 1 ∨ walshChar S x = -1 :=
  prod_sign S (fun i => bitSign (x i)) (fun i _ => bitSign_sign (x i))

theorem walshChar_sq {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) :
    walshChar S x ^ 2 = 1 := by
  rcases walshChar_sign S x with h | h <;> simp [h]

theorem walshChar_cross_zero_of_difference {d : ℕ}
    (S T : Finset (Fin d)) (j : Fin d) (hS : j ∈ S) (hT : j ∉ T) :
    (∑ x : Fin d → Bool, walshChar S x * walshChar T x) = 0 := by
  have he : (∑ x : Fin d → Bool,
      walshChar S (flipCoordinate j x) * walshChar T (flipCoordinate j x)) =
      ∑ x : Fin d → Bool, walshChar S x * walshChar T x :=
    Equiv.sum_comp (flipCoordinate j) (fun x => walshChar S x * walshChar T x)
  simp_rw [walshChar_flip S j hS, walshChar_flip_of_not_mem T j hT, neg_mul,
    Finset.sum_neg_distrib] at he
  omega

theorem walshChar_cross_zero {d : ℕ} (S T : Finset (Fin d)) (hne : S ≠ T) :
    (∑ x : Fin d → Bool, walshChar S x * walshChar T x) = 0 := by
  classical
  by_cases hST : S ⊆ T
  · have hTS : ¬T ⊆ S := fun h => hne (Finset.Subset.antisymm hST h)
    obtain ⟨j, hjT, hjS⟩ := Finset.not_subset.mp hTS
    simpa only [mul_comm] using walshChar_cross_zero_of_difference T S j hjT hjS
  · obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.mp hST
    exact walshChar_cross_zero_of_difference S T j hjS hjT

theorem walshChar_orthogonality {d : ℕ} (S T : Finset (Fin d)) :
    (∑ x : Fin d → Bool, walshChar S x * walshChar T x) =
      if S = T then (2 : ℤ) ^ d else 0 := by
  classical
  by_cases h : S = T
  · subst T
    simp only [ite_true]
    calc
      _ = ∑ _x : Fin d → Bool, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x _
        simpa only [pow_two] using walshChar_sq S x
      _ = _ := by simp
  · rw [ite_eq_right h]
    exact walshChar_cross_zero S T h

theorem walshChar_real_sum_zero {d : ℕ} (S : Finset (Fin d)) (hS : S.Nonempty) :
    (∑ x : Fin d → Bool, (walshChar S x : ℝ)) = 0 := by
  exact_mod_cast walshChar_sum_zero S hS

theorem walshChar_real_orthogonality {d : ℕ} (S T : Finset (Fin d)) :
    (∑ x : Fin d → Bool, (walshChar S x : ℝ) * (walshChar T x : ℝ)) =
      if S = T then (2 : ℝ) ^ d else 0 := by
  exact_mod_cast walshChar_orthogonality S T

theorem walshChar_singleton {d : ℕ} (i : Fin d) (x : Fin d → Bool) :
    walshChar {i} x = bitSign (x i) := by simp [walshChar]

theorem walshChar_pair {d : ℕ} (i j : Fin d) (hij : i ≠ j) (x : Fin d → Bool) :
    walshChar {i,j} x = bitSign (x i) * bitSign (x j) := by simp [walshChar,hij]

abbrev LowIndex (d : ℕ) := {S : Finset (Fin d) // S.Nonempty ∧ S.card ≤ 2}

def lowCharacter {d : ℕ} (i : LowIndex d) (x : Fin d → Bool) : ℝ :=
  (walshChar i.val x : ℝ)

theorem lowCharacter_zero {d : ℕ} (i : LowIndex d) :
    (∑ x, lowCharacter i x) = 0 :=
  walshChar_real_sum_zero i.val i.property.1

theorem lowCharacter_orthogonality {d : ℕ} (i j : LowIndex d) :
    (∑ x, lowCharacter i x * lowCharacter j x) =
      if i = j then (2 : ℝ) ^ d else 0 := by
  have h := walshChar_real_orthogonality i.val j.val
  simpa only [lowCharacter, Subtype.val_inj] using h

end EntropyDesigns
