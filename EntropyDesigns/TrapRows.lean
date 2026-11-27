module

public import EntropyDesigns.WalshInversion

/-! # Exact Gram geometry of the two-seed character trap -/

@[expose] public section
namespace EntropyDesigns

def trapMixed {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool)) : ℤ :=
  walshChar e u.1 * walshChar e u.2

def trapRow {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool)) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → ℤ :=
  Sum.elim (fun S => walshChar S u.1)
    (fun S => if S = ∅ then trapMixed e u else walshChar S u.2)

def trapInner {s : ℕ} (e : Finset (Fin s)) (u v : (Fin s → Bool) × (Fin s → Bool)) : ℤ :=
  ∑ j, trapRow e u j * trapRow e v j

theorem trapMixed_sign {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool)) :
    trapMixed e u = 1 ∨ trapMixed e u = -1 := by
  rcases walshChar_sign e u.1 with h | h <;> rcases walshChar_sign e u.2 with h' | h' <;>
    simp [trapMixed, h, h']

theorem trapMixed_sq {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool)) :
    trapMixed e u ^ 2 = 1 := by
  rcases trapMixed_sign e u with h | h <;> simp [h]

theorem trapRow_sign {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool))
    (j : Finset (Fin s) ⊕ Finset (Fin s)) : trapRow e u j = 1 ∨ trapRow e u j = -1 := by
  cases j with
  | inl S => exact walshChar_sign S u.1
  | inr S =>
    by_cases hS : S = ∅
    · simpa [trapRow, hS] using trapMixed_sign e u
    · simpa [trapRow, hS] using walshChar_sign S u.2

theorem trapInner_formula {s : ℕ} (e : Finset (Fin s))
    (u v : (Fin s → Bool) × (Fin s → Bool)) :
    trapInner e u v = (if u.1 = v.1 then (2 : ℤ) ^ s else 0) +
      (if u.2 = v.2 then (2 : ℤ) ^ s else 0) - 1 + trapMixed e u * trapMixed e v := by
  classical
  have hsecond : (∑ S : Finset (Fin s),
      (if S = ∅ then trapMixed e u else walshChar S u.2) *
      (if S = ∅ then trapMixed e v else walshChar S v.2)) =
      (∑ S : Finset (Fin s), walshChar S u.2 * walshChar S v.2) - 1 +
        trapMixed e u * trapMixed e v := by
    have hpoint : ∀ S : Finset (Fin s),
        (if S = ∅ then trapMixed e u else walshChar S u.2) *
          (if S = ∅ then trapMixed e v else walshChar S v.2) =
        walshChar S u.2 * walshChar S v.2 +
          if S = ∅ then trapMixed e u * trapMixed e v - 1 else 0 := by
      intro S
      by_cases hS : S = ∅ <;> simp [hS, walshChar]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp
    ring
  simp only [trapInner, trapRow, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [hsecond, walshChar_dual_orthogonality, walshChar_dual_orthogonality]
  ring

theorem two_pow_ge_four {s : ℕ} (hs : 2 ≤ s) : (4 : ℤ) ≤ 2 ^ s := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hs
  rw [hk, pow_add]
  have hpos : (0 : ℤ) < 2 ^ k := by positivity
  norm_num
  nlinarith

theorem trapInner_zero_iff {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (u v : (Fin s → Bool) × (Fin s → Bool)) :
    trapInner e u v = 0 ↔ u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ trapMixed e u = trapMixed e v := by
  classical
  have hM := two_pow_ge_four hs
  have hprod : -1 ≤ trapMixed e u * trapMixed e v := by
    rcases trapMixed_sign e u with h | h <;> rcases trapMixed_sign e v with h' | h' <;> simp [h, h']
  rw [trapInner_formula]
  constructor
  · intro h
    have ha : u.1 ≠ v.1 := by
      intro ha
      rw [ite_eq_left ha] at h
      by_cases hb : u.2 = v.2 <;> simp only [hb, ite_true, ite_false] at h <;> omega
    have hb : u.2 ≠ v.2 := by
      intro hb
      rw [ite_eq_right ha, ite_eq_left hb] at h
      omega
    refine ⟨ha, hb, ?_⟩
    rw [ite_eq_right ha, ite_eq_right hb] at h
    rcases trapMixed_sign e u with hu | hu <;> rcases trapMixed_sign e v with hv | hv <;>
      simp_all
  · rintro ⟨ha, hb, hmixed⟩
    rw [ite_eq_right ha, ite_eq_right hb, hmixed]
    nlinarith [trapMixed_sq e v]

theorem bitSign_injective : Function.Injective bitSign := by
  intro x y h
  cases x <;> cases y <;> simp_all [bitSign]

theorem walsh_characters_separate {s : ℕ} (x y : Fin s → Bool)
    (h : ∀ S : Finset (Fin s), walshChar S x = walshChar S y) : x = y := by
  funext i
  apply bitSign_injective
  simpa only [walshChar_singleton] using h {i}

theorem trapRow_injective {s : ℕ} (e : Finset (Fin s)) : Function.Injective (trapRow e) := by
  intro u v h
  apply Prod.ext
  · apply walsh_characters_separate
    intro S
    exact congrFun h (Sum.inl S)
  · apply walsh_characters_separate
    intro S
    by_cases hS : S = ∅
    · simp [hS, walshChar]
    · simpa [trapRow, hS] using congrFun h (Sum.inr S)

end EntropyDesigns
