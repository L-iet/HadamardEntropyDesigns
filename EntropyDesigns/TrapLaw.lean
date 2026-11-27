module

public import EntropyDesigns.TrapColumns
public import EntropyDesigns.BinaryObservables

/-! # The actual uniform probability law on the observed trap bits -/

@[expose] public section
namespace EntropyDesigns

abbrev TrapCoordinate (s : ℕ) :=
  {j : Finset (Fin s) ⊕ Finset (Fin s) // j ≠ Sum.inl ∅}

def trapCode {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) : TrapCoordinate s → Bool :=
  fun j => decide (trapRow e u j.val = -1)

theorem trapCode_sign {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : TrapCoordinate s) :
    bitSign (trapCode e u j) = trapRow e u j.val := by
  rcases trapRow_sign e u j.val with h | h <;> norm_num [trapCode, bitSign, h]

theorem trapCode_injective {s : ℕ} (e : Finset (Fin s)) : Function.Injective (trapCode e) := by
  intro u v huv
  apply trapRow_injective e
  funext j
  by_cases hj : j = Sum.inl ∅
  · subst j; simp [trapRow, walshChar]
  · have h := congrArg (fun x => bitSign (x ⟨j, hj⟩)) huv
    simpa only [trapCode_sign] using h

noncomputable def trapSeedWeight {s : ℕ} (_ : (Fin s → Bool) × (Fin s → Bool)) : ℝ :=
  1 / (Fintype.card ((Fin s → Bool) × (Fin s → Bool)) : ℝ)

noncomputable def trapLaw {s : ℕ} (e : Finset (Fin s)) : (TrapCoordinate s → Bool) → ℝ := by
  classical
  exact pushLaw (trapCode e) trapSeedWeight

theorem trap_seed_card (s : ℕ) :
    Fintype.card ((Fin s → Bool) × (Fin s → Bool)) = 2 ^ (2 * s) := by
  simp [Fintype.card_prod, two_mul, pow_add]

theorem trapSeedWeight_mass (s : ℕ) :
    (∑ u : (Fin s → Bool) × (Fin s → Bool), trapSeedWeight u) = 1 := by
  simp only [trapSeedWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem trapLaw_probability {s : ℕ} (e : Finset (Fin s)) :
    (∀ x, 0 ≤ trapLaw e x) ∧ (∑ x, trapLaw e x) = 1 := by
  classical
  constructor
  · exact pushLaw_nonneg _ _ (fun _ => by unfold trapSeedWeight; positivity)
  · exact (pushLaw_mass _ _).trans (trapSeedWeight_mass s)

theorem trapLaw_weights {s : ℕ} (e : Finset (Fin s)) :
    ∀ x, trapLaw e x = 0 ∨ trapLaw e x = 1 / (2 : ℝ) ^ (2 * s) := by
  classical
  apply pushLaw_injective_weights _ (trapCode_injective e)
  intro u
  simp only [trapSeedWeight, trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]

theorem trapLaw_support_card {s : ℕ} (e : Finset (Fin s)) :
    (Finset.univ.filter (fun x => trapLaw e x ≠ 0)).card = 2 ^ (2 * s) := by
  classical
  apply support_card_of_uniform_weights _ (2 ^ (2 * s)) (by positivity)
    (trapLaw_probability e).2
  intro x
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using trapLaw_weights e x

theorem trapLaw_collision {s : ℕ} (e : Finset (Fin s)) :
    collision (trapLaw e) = 1 / (2 : ℝ) ^ (2 * s) := by
  exact (entropy_of_uniform_weights _ (by positivity : (0 : ℝ) < 2 ^ (2 * s))
    (trapLaw_probability e).2 (trapLaw_weights e)).1

theorem trapSeedWeight_isotropic {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (i j : Finset (Fin s) ⊕ Finset (Fin s)) :
    (∑ u : (Fin s → Bool) × (Fin s → Bool),
      trapSeedWeight u * (trapRow e u i : ℝ) * (trapRow e u j : ℝ)) =
      if i = j then 1 else 0 := by
  have hc : (∑ u : (Fin s → Bool) × (Fin s → Bool),
      (trapRow e u i : ℝ) * (trapRow e u j : ℝ)) =
      if i = j then (2 : ℝ) ^ (2 * s) else 0 := by
    exact_mod_cast trap_columns_orthogonal e he i j
  unfold trapSeedWeight
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hc]
  simp only [trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
  by_cases h : i = j <;> simp [h]

theorem trapLaw_mean {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (j : TrapCoordinate s) :
    (∑ x : TrapCoordinate s → Bool, trapLaw e x * (bitSign (x j) : ℝ)) = 0 := by
  classical
  have h := trapSeedWeight_isotropic e he (Sum.inl ∅) j.val
  have hj : (Sum.inl ∅ : Finset (Fin s) ⊕ Finset (Fin s)) ≠ j.val := Ne.symm j.property
  have hconst : ∀ u : (Fin s → Bool) × (Fin s → Bool), trapRow e u (Sum.inl ∅) = 1 := by
    intro u; simp [trapRow, walshChar]
  simp only [hj, ite_false, hconst, Int.cast_one, mul_one] at h
  change (∑ x, pushLaw (trapCode e) trapSeedWeight x * (bitSign (x j) : ℝ)) = 0
  rw [pushLaw_moment]
  simpa only [trapCode_sign] using h

theorem trapLaw_pair {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (i j : TrapCoordinate s) (hij : i ≠ j) :
    (∑ x : TrapCoordinate s → Bool,
      trapLaw e x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) = 0 := by
  classical
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have h := trapSeedWeight_isotropic e he i.val j.val
  rw [ite_eq_right hval] at h
  simp_rw [mul_assoc] at h ⊢
  change (∑ x, pushLaw (trapCode e) trapSeedWeight x *
    ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0
  rw [pushLaw_moment]
  simpa only [trapCode_sign] using h

end EntropyDesigns
