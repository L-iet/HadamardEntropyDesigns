module

public import EntropyDesigns.TrapEndpoint

/-! # The actual intermediate character masks in the finite rewiring -/

@[expose] public section
namespace EntropyDesigns

def rewireMask {s : ℕ} (e : Finset (Fin s)) (T : Finset (Finset (Fin s))) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s) :=
  Sum.elim (fun S => (S, ∅))
    (fun S => if S = ∅ then (∅, e) else if S = e ∨ S ∈ T then (S, e) else (∅, S))

def rewireDecode {s : ℕ} (e : Finset (Fin s))
    (P : Finset (Fin s) × Finset (Fin s)) : Finset (Fin s) ⊕ Finset (Fin s) :=
  if P.2 = ∅ then Sum.inl P.1 else
    if P.1 = ∅ then (if P.2 = e then Sum.inr ∅ else Sum.inr P.2) else Sum.inr P.1

theorem rewireDecode_left_inverse {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (T : Finset (Finset (Fin s))) : Function.LeftInverse (rewireDecode e) (rewireMask e T) := by
  intro j
  have hne := he.ne_empty
  cases j with
  | inl S => simp [rewireMask, rewireDecode]
  | inr S =>
    by_cases hs : S = ∅
    · simp [rewireMask, rewireDecode, hs, hne]
    · by_cases hmod : S = e ∨ S ∈ T
      · simp [rewireMask, rewireDecode, hs, hmod, hne]
      · have hse : S ≠ e := fun h => hmod (Or.inl h)
        have hT : S ∉ T := fun h => hmod (Or.inr h)
        simp [rewireMask, rewireDecode, hs, hse, hT]

theorem rewireMask_injective {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (T : Finset (Finset (Fin s))) : Function.Injective (rewireMask e T) :=
  (rewireDecode_left_inverse e he T).injective

theorem rewireMask_constant {s : ℕ} (e : Finset (Fin s)) (T : Finset (Finset (Fin s))) :
    rewireMask e T (Sum.inl ∅) = (∅, ∅) := rfl

theorem rewireMask_observed_nonzero {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (T : Finset (Finset (Fin s))) (j : TrapCoordinate s) :
    rewireMask e T j.val ≠ (∅, ∅) := by
  intro h
  have hc := rewireMask_constant e T
  exact j.property (rewireMask_injective e he T (h.trans hc.symm))

theorem rewireMask_old_column {s : ℕ} (e b : Finset (Fin s))
    (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) (hbe : b ≠ e) (hbT : b ∉ T) :
    rewireMask e T (Sum.inr b) = (∅, b) := by
  simp [rewireMask, hb, hbe, hbT]

theorem rewireMask_insert {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s)))
    (hb : b ≠ ∅) : rewireMask e (insert b T) =
      Function.update (rewireMask e T) (Sum.inr b) (b, e) := by
  funext j
  cases j with
  | inl S => simp [rewireMask]
  | inr S =>
    by_cases hs : S = b
    · subst S; simp [rewireMask, hb]
    · have hsum : (Sum.inr S : Finset (Fin s) ⊕ Finset (Fin s)) ≠ Sum.inr b := by simpa
      rw [Function.update_of_ne hsum]
      simp [rewireMask, hs]

def initialSwapIndex {s : ℕ} (e : Finset (Fin s)) :
    (Finset (Fin s) ⊕ Finset (Fin s)) ≃ (Finset (Fin s) ⊕ Finset (Fin s)) :=
  Equiv.swap (Sum.inr ∅) (Sum.inr e)

theorem rewireMask_initial_swap {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    rewireMask e ∅ = trapMask e ∘ initialSwapIndex e := by
  funext j
  have hne := he.ne_empty
  cases j with
  | inl S => simp [initialSwapIndex, Equiv.swap_apply_def, rewireMask, trapMask]
  | inr S =>
    by_cases hs : S = ∅ <;> by_cases hse : S = e <;>
      simp_all [initialSwapIndex, Equiv.swap_apply_def, rewireMask, trapMask]

end EntropyDesigns
