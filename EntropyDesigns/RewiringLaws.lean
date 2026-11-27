module

public import EntropyDesigns.RewiringMasks
public import EntropyDesigns.MaskPairLaw

/-! # Feasible rewiring endpoints and their exact observed coordinates -/

@[expose] public section
namespace EntropyDesigns

noncomputable def rewireLaw {s : ℕ} (e : Finset (Fin s)) (T : Finset (Finset (Fin s))) :
    (TrapCoordinate s → Bool) → ℝ := maskPairLaw (rewireMask e T)

theorem rewireLaw_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (T : Finset (Finset (Fin s))) : observedFeasible (rewireLaw e T) :=
  maskPairLaw_feasible _ (rewireMask_injective e he T) (rewireMask_constant e T)

theorem rewireCode_unchanged_column {s : ℕ} (e b : Finset (Fin s))
    (T : Finset (Finset (Fin s))) (hb : b ≠ ∅)
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : TrapCoordinate s) (hj : j.val ≠ Sum.inr b) :
    maskPairCode (rewireMask e (insert b T)) u j = maskPairCode (rewireMask e T) u j := by
  apply bitSign_injective
  rw [maskPairCode_sign, maskPairCode_sign]
  unfold maskPairRow
  rw [rewireMask_insert e b T hb]
  simp only [Function.update_of_ne hj]

theorem rewireCode_new_column {s : ℕ} (e b : Finset (Fin s))
    (T : Finset (Finset (Fin s))) (hb : b ≠ ∅)
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : TrapCoordinate s) (hj : j.val = Sum.inr b) :
    bitSign (maskPairCode (rewireMask e (insert b T)) u j) = walshChar b u.1 * walshChar e u.2 := by
  rw [maskPairCode_sign]
  simp [maskPairRow, hj, rewireMask, hb]

theorem rewireRow_initial_swap {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) :
    maskPairRow (rewireMask e ∅) u j = trapRow e u (initialSwapIndex e j) := by
  rw [trapRow_mask, rewireMask_initial_swap e he]
  rfl

def rewireEndpointSeed {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) : (Fin s → Bool) × Bool :=
  (u.1, decide (walshChar e u.2 = -1))

theorem rewireEndpointSeed_sign {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) :
    bitSign (rewireEndpointSeed e u).2 = walshChar e u.2 := by
  rcases walshChar_sign e u.2 with h | h <;> norm_num [rewireEndpointSeed, bitSign, h]

theorem rewireRow_final {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) :
    maskPairRow (rewireMask e Finset.univ) u j = endpointRow (rewireEndpointSeed e u) j := by
  cases j with
  | inl S => simp [maskPairRow, rewireMask, endpointRow, rewireEndpointSeed, walshChar]
  | inr S =>
    have ht := rewireEndpointSeed_sign e u
    change _ = bitSign (rewireEndpointSeed e u).2 * walshChar S u.1
    rw [ht]
    by_cases hs : S = ∅ <;> simp [maskPairRow, rewireMask, hs, walshChar, mul_comm]

theorem rewireCode_final {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) :
    maskPairCode (rewireMask e Finset.univ) u = endpointCode (rewireEndpointSeed e u) := by
  funext j
  apply bitSign_injective
  rw [maskPairCode_sign, endpointCode_sign, rewireRow_final]

theorem pushLaw_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (w : α → ℝ) (z : γ) :
    pushLaw g (pushLaw f w) z = pushLaw (g ∘ f) w z := by
  have h := pushLaw_moment f w (fun y => if g y = z then 1 else 0)
  simpa only [pushLaw, mul_ite, mul_one, mul_zero, Function.comp_apply] using h

theorem rewireEndpointSeed_weights {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (a : Fin s → Bool) (t : Bool) :
    pushLaw (rewireEndpointSeed e) trapSeedWeight (a, t) = endpointSeedWeight (a, t) := by
  classical
  have hbit : ∀ b : Fin s → Bool, decide (walshChar e b = -1) = t ↔ walshChar e b = bitSign t := by
    intro b
    cases t <;> rcases walshChar_sign e b with h | h <;> norm_num [h, bitSign]
  have hterm : ∀ a' b : Fin s → Bool,
      (if rewireEndpointSeed e (a', b) = (a, t) then trapSeedWeight (a', b) else 0) =
      if a' = a then (if walshChar e b = bitSign t then 1 / (2 : ℝ) ^ (2 * s) else 0) else 0 := by
    intro a' b
    simp only [rewireEndpointSeed, Prod.mk.injEq, hbit, trapSeedWeight,
      trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
    by_cases ha : a' = a <;> simp [ha]
  unfold pushLaw
  rw [Fintype.sum_prod_type]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hsum : (∑ b : Fin s → Bool,
      if walshChar e b = bitSign t then 1 / (2 : ℝ) ^ (2 * s) else 0) =
      ((characterLevel e (bitSign t)).card : ℝ) / (2 : ℝ) ^ (2 * s) := by
    simp [characterLevel, Finset.sum_ite, div_eq_mul_inv]
  rw [hsum]
  have hc : (2 : ℝ) * ((characterLevel e (bitSign t)).card : ℝ) = (2 : ℝ) ^ s := by
    exact_mod_cast characterLevel_double_card e he (bitSign t) (bitSign_sign t)
  have hc' : ((characterLevel e (bitSign t)).card : ℝ) = (2 : ℝ) ^ s / 2 := by linarith
  have hp : (2 : ℝ) ^ (2 * s) = ((2 : ℝ) ^ s) ^ 2 := by rw [two_mul, pow_add, pow_two]
  rw [hc', hp]
  simp only [endpointSeedWeight, endpoint_seed_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem rewireLaw_final {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    rewireLaw e Finset.univ = endpointLaw s := by
  classical
  have hcode : maskPairCode (rewireMask e Finset.univ) = endpointCode ∘ rewireEndpointSeed e := by
    funext u
    exact rewireCode_final e u
  have hseed : pushLaw (rewireEndpointSeed e) trapSeedWeight = @endpointSeedWeight s := by
    funext u
    exact rewireEndpointSeed_weights e he u.1 u.2
  funext x
  change pushLaw (maskPairCode (rewireMask e Finset.univ)) trapSeedWeight x =
    pushLaw endpointCode endpointSeedWeight x
  rw [hcode, ← pushLaw_comp, hseed]

end EntropyDesigns
