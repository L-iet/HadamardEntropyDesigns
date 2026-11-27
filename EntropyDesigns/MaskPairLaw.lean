module

public import EntropyDesigns.TrapOptimizers

/-! # Actual feasible laws from injective lists of two-seed characters -/

@[expose] public section
namespace EntropyDesigns

def maskPairRow {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) : ℤ :=
  walshChar (M j).1 u.1 * walshChar (M j).2 u.2

theorem maskPairRow_sign {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) :
    maskPairRow M u j = 1 ∨ maskPairRow M u j = -1 := by
  rcases walshChar_sign (M j).1 u.1 with h1 | h1 <;>
    rcases walshChar_sign (M j).2 u.2 with h2 | h2 <;> simp [maskPairRow, h1, h2]

def maskPairCode {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) : TrapCoordinate s → Bool :=
  fun j => decide (maskPairRow M u j.val = -1)

theorem maskPairCode_sign {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : TrapCoordinate s) :
    bitSign (maskPairCode M u j) = maskPairRow M u j.val := by
  rcases maskPairRow_sign M u j.val with h | h <;> norm_num [maskPairCode, bitSign, h]

noncomputable def maskPairLaw {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    (TrapCoordinate s → Bool) → ℝ := by
  classical
  exact pushLaw (maskPairCode M) trapSeedWeight

theorem maskPairRow_isotropic {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (hinj : Function.Injective M) (i j : Finset (Fin s) ⊕ Finset (Fin s)) :
    (∑ u : (Fin s → Bool) × (Fin s → Bool),
      trapSeedWeight u * (maskPairRow M u i : ℝ) * (maskPairRow M u j : ℝ)) =
      if i = j then 1 else 0 := by
  have hc : (∑ u : (Fin s → Bool) × (Fin s → Bool),
      (maskPairRow M u i : ℝ) * (maskPairRow M u j : ℝ)) =
      if i = j then (2 : ℝ) ^ (2 * s) else 0 := by
    have hi := two_seed_character_orthogonality (M i) (M j)
    simp only [hinj.eq_iff] at hi
    exact_mod_cast hi
  unfold trapSeedWeight
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hc]
  simp only [trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
  by_cases h : i = j <;> simp [h]

theorem maskPairLaw_feasible {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (hinj : Function.Injective M) (hzero : M (Sum.inl ∅) = (∅, ∅)) :
    observedFeasible (maskPairLaw M) := by
  classical
  have hconst : ∀ u : (Fin s → Bool) × (Fin s → Bool), maskPairRow M u (Sum.inl ∅) = 1 := by
    intro u; simp [maskPairRow, hzero, walshChar]
  refine ⟨pushLaw_nonneg _ _ (fun _ => by unfold trapSeedWeight; positivity),
    (pushLaw_mass _ _).trans (trapSeedWeight_mass s), ?_, ?_⟩
  · intro j
    have h := maskPairRow_isotropic M hinj (Sum.inl ∅) j.val
    have hj : (Sum.inl ∅ : Finset (Fin s) ⊕ Finset (Fin s)) ≠ j.val := Ne.symm j.property
    simp only [hj, ite_false, hconst, Int.cast_one, mul_one] at h
    change (∑ x, pushLaw (maskPairCode M) trapSeedWeight x * (bitSign (x j) : ℝ)) = 0
    rw [pushLaw_moment]
    simpa only [maskPairCode_sign] using h
  · intro i j hij
    have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    have h := maskPairRow_isotropic M hinj i.val j.val
    rw [ite_eq_right hval] at h
    simp_rw [mul_assoc] at h ⊢
    change (∑ x, pushLaw (maskPairCode M) trapSeedWeight x *
      ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0
    rw [pushLaw_moment]
    simpa only [maskPairCode_sign] using h

end EntropyDesigns
