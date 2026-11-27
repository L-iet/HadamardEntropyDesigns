module

public import EntropyDesigns.TrapRows
public import EntropyDesigns.Pushforward

/-! # Exact column orthogonality for the two-seed trap -/

@[expose] public section
namespace EntropyDesigns

def trapMask {s : ℕ} (e : Finset (Fin s)) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s) :=
  Sum.elim (fun S => (S, ∅)) (fun S => if S = ∅ then (e, e) else (∅, S))

theorem trapMask_injective {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    Function.Injective (trapMask e) := by
  have hne : e ≠ ∅ := he.ne_empty
  intro i j h
  cases i with
  | inl S =>
    cases j with
    | inl T => exact congrArg Sum.inl (congrArg Prod.fst h)
    | inr T =>
      by_cases ht : T = ∅
      · have hh := congrArg Prod.snd h
        simp [trapMask, ht] at hh
        exact False.elim (hne hh.symm)
      · have hh := congrArg Prod.snd h
        simp [trapMask, ht] at hh
        exact False.elim (ht hh.symm)
  | inr S =>
    cases j with
    | inl T =>
      by_cases hs : S = ∅
      · have hh := congrArg Prod.snd h
        simp [trapMask, hs, hne] at hh
      · have hh := congrArg Prod.snd h
        simp [trapMask, hs] at hh
    | inr T =>
      by_cases hs : S = ∅ <;> by_cases ht : T = ∅
      · simp [hs, ht]
      · have hh := congrArg Prod.fst h
        simp [trapMask, hs, ht] at hh
        exact False.elim (hne hh)
      · have hh := congrArg Prod.fst h
        simp [trapMask, hs, ht] at hh
        exact False.elim (hne hh.symm)
      · exact congrArg Sum.inr (by simpa [trapMask, hs, ht] using congrArg Prod.snd h)

theorem trapRow_mask {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) :
    trapRow e u j = walshChar (trapMask e j).1 u.1 * walshChar (trapMask e j).2 u.2 := by
  cases j with
  | inl S => simp [trapRow, trapMask, walshChar]
  | inr S => by_cases h : S = ∅ <;> simp [trapRow, trapMask, trapMixed, h, walshChar]

theorem two_seed_character_orthogonality {s : ℕ}
    (P Q : Finset (Fin s) × Finset (Fin s)) :
    (∑ u : (Fin s → Bool) × (Fin s → Bool),
      (walshChar P.1 u.1 * walshChar P.2 u.2) *
        (walshChar Q.1 u.1 * walshChar Q.2 u.2)) =
      if P = Q then (2 : ℤ) ^ (2 * s) else 0 := by
  rw [Fintype.sum_prod_type]
  have hp : ∀ a b, (walshChar P.1 a * walshChar P.2 b) *
      (walshChar Q.1 a * walshChar Q.2 b) =
      (walshChar P.1 a * walshChar Q.1 a) * (walshChar P.2 b * walshChar Q.2 b) := by
    intro a b; ring
  simp_rw [hp, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [walshChar_orthogonality, walshChar_orthogonality]
  rcases P with ⟨P1, P2⟩
  rcases Q with ⟨Q1, Q2⟩
  by_cases h1 : P1 = Q1 <;> by_cases h2 : P2 = Q2 <;>
    simp [h1, h2, Prod.mk.injEq, two_mul, pow_add]

theorem trap_columns_orthogonal {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (i j : Finset (Fin s) ⊕ Finset (Fin s)) :
    (∑ u : (Fin s → Bool) × (Fin s → Bool), trapRow e u i * trapRow e u j) =
      if i = j then (2 : ℤ) ^ (2 * s) else 0 := by
  simp_rw [trapRow_mask]
  rw [two_seed_character_orthogonality]
  simp only [(trapMask_injective e he).eq_iff]

end EntropyDesigns
