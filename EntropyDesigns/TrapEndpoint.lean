module

public import EntropyDesigns.TrapLaw

/-! # The explicit compressed endpoint on the same observed coordinates -/

@[expose] public section
namespace EntropyDesigns

def endpointRow {s : ℕ} (u : (Fin s → Bool) × Bool) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → ℤ :=
  Sum.elim (fun S => walshChar S u.1) (fun S => bitSign u.2 * walshChar S u.1)

theorem endpointRow_sign {s : ℕ} (u : (Fin s → Bool) × Bool)
    (j : Finset (Fin s) ⊕ Finset (Fin s)) : endpointRow u j = 1 ∨ endpointRow u j = -1 := by
  cases j with
  | inl S => exact walshChar_sign S u.1
  | inr S =>
    rcases bitSign_sign u.2 with h1 | h1 <;> rcases walshChar_sign S u.1 with h2 | h2 <;>
      simp [endpointRow, h1, h2]

def endpointCode {s : ℕ} (u : (Fin s → Bool) × Bool) : TrapCoordinate s → Bool :=
  fun j => decide (endpointRow u j.val = -1)

theorem endpointCode_sign {s : ℕ} (u : (Fin s → Bool) × Bool) (j : TrapCoordinate s) :
    bitSign (endpointCode u j) = endpointRow u j.val := by
  rcases endpointRow_sign u j.val with h | h <;> norm_num [endpointCode, bitSign, h]

theorem endpointCode_injective {s : ℕ} : Function.Injective (@endpointCode s) := by
  intro u v huv
  have hrow : ∀ j, endpointRow u j = endpointRow v j := by
    intro j
    by_cases hj : j = Sum.inl ∅
    · subst j; simp [endpointRow, walshChar]
    · simpa only [endpointCode_sign] using congrArg (fun x => bitSign (x ⟨j, hj⟩)) huv
  apply Prod.ext
  · apply walsh_characters_separate
    intro S
    exact hrow (Sum.inl S)
  · apply bitSign_injective
    simpa [endpointRow, walshChar] using hrow (Sum.inr ∅)

theorem sum_bool_int (f : Bool → ℤ) : (∑ t, f t) = f false + f true := by
  have h : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [h]
  simp

theorem endpoint_columns_orthogonal {s : ℕ}
    (i j : Finset (Fin s) ⊕ Finset (Fin s)) :
    (∑ u : (Fin s → Bool) × Bool, endpointRow u i * endpointRow u j) =
      if i = j then (2 : ℤ) * 2 ^ s else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_bool_int]
  cases i with
  | inl S =>
    cases j with
    | inl T =>
      simp only [endpointRow, Sum.elim_inl, Sum.inl.injEq]
      rw [Finset.sum_add_distrib, walshChar_orthogonality]
      split_ifs <;> ring
    | inr T => simp [endpointRow, bitSign]
  | inr S =>
    cases j with
    | inl T => simp [endpointRow, bitSign]
    | inr T =>
      simp only [endpointRow, Sum.elim_inr, Sum.inr.injEq, bitSign, Bool.false_eq_true,
        ite_false, ite_true, one_mul, neg_one_mul, neg_mul_neg]
      rw [Finset.sum_add_distrib, walshChar_orthogonality]
      split_ifs <;> ring

noncomputable def endpointSeedWeight {s : ℕ} (_ : (Fin s → Bool) × Bool) : ℝ :=
  1 / (Fintype.card ((Fin s → Bool) × Bool) : ℝ)

noncomputable def endpointLaw (s : ℕ) : (TrapCoordinate s → Bool) → ℝ := by
  classical
  exact pushLaw endpointCode endpointSeedWeight

theorem endpoint_seed_card (s : ℕ) : Fintype.card ((Fin s → Bool) × Bool) = 2 * 2 ^ s := by
  simp [Fintype.card_prod, Nat.mul_comm]

theorem endpointSeedWeight_mass (s : ℕ) :
    (∑ u : (Fin s → Bool) × Bool, endpointSeedWeight u) = 1 := by
  simp only [endpointSeedWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    endpoint_seed_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem endpointLaw_probability (s : ℕ) :
    (∀ x, 0 ≤ endpointLaw s x) ∧ (∑ x, endpointLaw s x) = 1 := by
  classical
  constructor
  · exact pushLaw_nonneg _ _ (fun _ => by unfold endpointSeedWeight; positivity)
  · exact (pushLaw_mass _ _).trans (endpointSeedWeight_mass s)

theorem endpointLaw_weights (s : ℕ) :
    ∀ x, endpointLaw s x = 0 ∨ endpointLaw s x = 1 / (2 * (2 : ℝ) ^ s) := by
  classical
  apply pushLaw_injective_weights _ endpointCode_injective
  intro u
  simp only [endpointSeedWeight, endpoint_seed_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem endpointLaw_support_card (s : ℕ) :
    (Finset.univ.filter (fun x => endpointLaw s x ≠ 0)).card = 2 * 2 ^ s := by
  classical
  apply support_card_of_uniform_weights _ (2 * 2 ^ s) (by positivity) (endpointLaw_probability s).2
  intro x
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using endpointLaw_weights s x

theorem endpointLaw_collision (s : ℕ) : collision (endpointLaw s) = 1 / (2 * (2 : ℝ) ^ s) := by
  exact (entropy_of_uniform_weights _ (by positivity : (0 : ℝ) < 2 * 2 ^ s)
    (endpointLaw_probability s).2 (endpointLaw_weights s)).1

theorem endpointSeedWeight_isotropic {s : ℕ}
    (i j : Finset (Fin s) ⊕ Finset (Fin s)) :
    (∑ u : (Fin s → Bool) × Bool,
      endpointSeedWeight u * (endpointRow u i : ℝ) * (endpointRow u j : ℝ)) =
      if i = j then 1 else 0 := by
  have hc : (∑ u : (Fin s → Bool) × Bool,
      (endpointRow u i : ℝ) * (endpointRow u j : ℝ)) =
      if i = j then (2 : ℝ) * 2 ^ s else 0 := by
    exact_mod_cast endpoint_columns_orthogonal i j
  unfold endpointSeedWeight
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, hc]
  simp only [endpoint_seed_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h]
    field_simp
  · simp [h]

theorem endpointLaw_mean {s : ℕ} (j : TrapCoordinate s) :
    (∑ x : TrapCoordinate s → Bool, endpointLaw s x * (bitSign (x j) : ℝ)) = 0 := by
  classical
  have h := endpointSeedWeight_isotropic (Sum.inl ∅) j.val
  have hj : (Sum.inl ∅ : Finset (Fin s) ⊕ Finset (Fin s)) ≠ j.val := Ne.symm j.property
  have hconst : ∀ u : (Fin s → Bool) × Bool, endpointRow u (Sum.inl ∅) = 1 := by
    intro u; simp [endpointRow, walshChar]
  simp only [hj, ite_false, hconst, Int.cast_one, mul_one] at h
  change (∑ x, pushLaw endpointCode endpointSeedWeight x * (bitSign (x j) : ℝ)) = 0
  rw [pushLaw_moment]
  simpa only [endpointCode_sign] using h

theorem endpointLaw_pair {s : ℕ} (i j : TrapCoordinate s) (hij : i ≠ j) :
    (∑ x : TrapCoordinate s → Bool,
      endpointLaw s x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) = 0 := by
  classical
  have hval : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  have h := endpointSeedWeight_isotropic i.val j.val
  rw [ite_eq_right hval] at h
  simp_rw [mul_assoc] at h ⊢
  change (∑ x, pushLaw endpointCode endpointSeedWeight x *
    ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0
  rw [pushLaw_moment]
  simpa only [endpointCode_sign] using h

end EntropyDesigns
