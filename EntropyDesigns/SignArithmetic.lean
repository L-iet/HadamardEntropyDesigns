module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

/-! # Exact sign arithmetic behind the residue-sensitive collision bounds -/

@[expose] public section
namespace EntropyDesigns

/-- A finite product of integer signs is an integer sign. -/
theorem prod_sign {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∏ i ∈ s, f i) = 1 ∨ (∏ i ∈ s, f i) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha]
      rcases hfa with h | h <;> rcases hfs with h' | h' <;> simp [h, h']

/-- The sum is congruent to cardinality minus one plus product modulo four. -/
theorem sign_sum_mod_four {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) :
    (∑ i ∈ s, f i) % 4 = ((s.card : ℤ) - 1 + ∏ i ∈ s, f i) % 4 := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num
  | @insert a s ha ih =>
      have hfa := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i = 1 ∨ f i = -1 :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum := ih hfs
      have hp := prod_sign s f hfs
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      push_cast
      rcases hfa with h | h <;> rcases hp with h' | h' <;>
        simp only [h, h', one_mul, neg_one_mul] at * <;> omega

/-- Odd-dimensional sign inner products have nonzero integer square. -/
theorem odd_sign_sum_square_ge_one {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hn : s.card % 2 = 1) :
    1 ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hs := sign_sum_mod_four s f hf
  have hp := prod_sign s f hf
  have hz : (∑ i ∈ s, f i) ≠ 0 := by
    rcases hp with hp | hp <;> rw [hp] at hs <;> omega
  have h : (∑ i ∈ s, f i) ≤ -1 ∨ 1 ≤ (∑ i ∈ s, f i) := by omega
  rcases h with h | h <;> nlinarith

/-- The product switch puts the residue-one signed sum in residue one. -/
theorem switched_sign_sum_mod_four {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hn : s.card % 4 = 1) :
    ((∏ i ∈ s, f i) * (∑ i ∈ s, f i)) % 4 = 1 := by
  have hs := sign_sum_mod_four s f hf
  have hp := prod_sign s f hf
  rcases hp with hp | hp
  · rw [hp] at hs ⊢
    simp only [one_mul]
    omega
  · rw [hp] at hs ⊢
    simp only [neg_one_mul]
    omega

/-- The nonnegative polynomial used in the difficult residue class. -/
theorem residue_one_polynomial_nonneg (q : ℤ) (hq : q % 4 = 1) :
    0 ≤ q ^ 2 + 2 * q - 3 := by
  have h : q ≤ -3 ∨ 1 ≤ q := by omega
  rcases h with h | h <;> nlinarith

/-- The two-parity-class pointwise estimate in dimension two modulo four. -/
theorem residue_two_sign_square_lower {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hn : s.card % 4 = 2) :
    2 + 2 * (∏ i ∈ s, f i) ≤ (∑ i ∈ s, f i) ^ 2 := by
  have hs := sign_sum_mod_four s f hf
  rcases prod_sign s f hf with hp | hp
  · rw [hp] at hs ⊢
    have h : (∑ i ∈ s, f i) ≤ -2 ∨ 2 ≤ (∑ i ∈ s, f i) := by omega
    rcases h with h | h <;> nlinarith
  · rw [hp]
    nlinarith [sq_nonneg (∑ i ∈ s, f i)]

end EntropyDesigns
