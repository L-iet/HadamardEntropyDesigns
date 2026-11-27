module

public import EntropyDesigns.RewiringCounts
public import EntropyDesigns.LinearOverlap

/-! # The exact cross inner product at the initial two-column swap -/

@[expose] public section
namespace EntropyDesigns

theorem omitted_character_separation {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (a b : Fin s → Bool) (h : ∀ S : Finset (Fin s), S ≠ e → walshChar S a = walshChar S b) : a = b := by
  classical
  by_contra hab
  have hfull := walshChar_dual_orthogonality a b
  rw [ite_eq_right hab] at hfull
  have hrem : (∑ S ∈ (Finset.univ : Finset (Finset (Fin s))).erase e,
      walshChar S a * walshChar S b) =
      (((Finset.univ : Finset (Finset (Fin s))).erase e).card : ℤ) := by
    calc
      _ = ∑ S ∈ (Finset.univ : Finset (Finset (Fin s))).erase e, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [h S (Finset.mem_erase.mp hS).1, ← pow_two, walshChar_sq]
      _ = _ := by simp
  have hcard : (((Finset.univ : Finset (Finset (Fin s))).erase e).card : ℤ) + 1 = (2 : ℤ) ^ s := by
    have hc := Finset.card_erase_add_one (s := (Finset.univ : Finset (Finset (Fin s))))
      (Finset.mem_univ e)
    have hc' : ((Finset.univ : Finset (Finset (Fin s))).erase e).card + 1 = 2 ^ s := by simpa using hc
    exact_mod_cast hc'
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin s)))
    (fun S => walshChar S a * walshChar S b) (Finset.mem_univ e)
  rw [hrem, hfull] at hsplit
  have hpow := two_pow_ge_four hs
  rcases walshChar_sign e a with ha | ha <;> rcases walshChar_sign e b with hb | hb <;>
    rw [ha, hb] at hsplit <;> norm_num at hsplit <;> omega

theorem trap_swap_code_eq_iff {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (a b c d : Fin s → Bool) :
    trapCode e (a, b) = maskPairCode (rewireMask e ∅) (c, d) ↔ a = c ∧ b = d ∧ walshChar e a = 1 := by
  have hempty : ∀ x : Fin s → Bool, walshChar ∅ x = 1 := by intro x; simp [walshChar]
  constructor
  · intro hcode
    have hrow : ∀ j, trapRow e (a, b) j = maskPairRow (rewireMask e ∅) (c, d) j := by
      intro j
      by_cases hj : j = Sum.inl ∅
      · subst j; simp [trapRow, maskPairRow, rewireMask, hempty]
      · simpa only [trapCode_sign, maskPairCode_sign] using
          congrArg (fun x => bitSign (x ⟨j, hj⟩)) hcode
    have hac : a = c := by
      apply walsh_characters_separate
      intro S
      simpa [trapRow, maskPairRow, rewireMask, hempty] using hrow (Sum.inl S)
    have hbd : b = d := by
      apply omitted_character_separation hs e
      intro S hSe
      by_cases hS : S = ∅
      · simp [hS, hempty]
      · simpa [trapRow, maskPairRow, rewireMask, hS, hSe, hempty] using hrow (Sum.inr S)
    have hm := hrow (Sum.inr ∅)
    simp only [trapRow, Sum.elim_inr, ite_true, trapMixed, maskPairRow, rewireMask,
      hempty, one_mul, hbd] at hm
    have hchi : walshChar e a = 1 := by
      rcases walshChar_sign e d with hd | hd <;> rw [hd] at hm <;> nlinarith
    exact ⟨hac, hbd, hchi⟩
  · rintro ⟨rfl, rfl, hchi⟩
    funext j
    apply bitSign_injective
    rw [trapCode_sign, maskPairCode_sign]
    rcases j with ⟨j, hj⟩
    cases j with
    | inl S => simp [trapRow, maskPairRow, rewireMask, hempty]
    | inr S =>
      by_cases hS : S = ∅
      · simp [trapRow, maskPairRow, rewireMask, trapMixed, hS, hchi, hempty]
      · by_cases hSe : S = e
        · have hene : e ≠ ∅ := fun h => hS (hSe.trans h)
          simp [trapRow, maskPairRow, rewireMask, trapMixed, hSe, hene, hchi]
        · simp [trapRow, maskPairRow, rewireMask, trapMixed, hS, hSe, hchi, hempty]

theorem trapLaw_at_swap {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (a b : Fin s → Bool) :
    trapLaw e (maskPairCode (rewireMask e ∅) (a, b)) =
      if walshChar e a = 1 then 1 / (2 : ℝ) ^ (2 * s) else 0 := by
  classical
  by_cases ha : walshChar e a = 1
  · have heq := (trap_swap_code_eq_iff hs e a b a b).mpr ⟨rfl, rfl, ha⟩
    change pushLaw (trapCode e) trapSeedWeight _ = _
    rw [← heq, pushLaw_injective_value _ (trapCode_injective e)]
    simp only [trapSeedWeight, trap_seed_card, Nat.cast_pow, Nat.cast_ofNat, ha, ite_true]
  · have hn : ∀ u : (Fin s → Bool) × (Fin s → Bool),
        trapCode e u ≠ maskPairCode (rewireMask e ∅) (a, b) := by
      rintro ⟨c, d⟩ hc
      have hh := (trap_swap_code_eq_iff hs e c d a b).mp hc
      exact ha (hh.1 ▸ hh.2.2)
    simp [trapLaw, pushLaw, hn, ha]

theorem initial_swap_lawOverlap {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    lawOverlap (trapLaw e) (rewireLaw e ∅) = 1 / (2 * (2 : ℝ) ^ (2 * s)) := by
  classical
  have hp := pushLaw_moment (maskPairCode (rewireMask e ∅)) (@trapSeedWeight s) (trapLaw e)
  have hdot : lawOverlap (trapLaw e) (rewireLaw e ∅) =
      ∑ u : (Fin s → Bool) × (Fin s → Bool),
        trapSeedWeight u * trapLaw e (maskPairCode (rewireMask e ∅) u) := by
    unfold lawOverlap
    rw [← hp]
    apply Finset.sum_congr rfl
    intro x hx
    unfold rewireLaw maskPairLaw
    ring
  rw [hdot, Fintype.sum_prod_type]
  simp_rw [trapLaw_at_swap hs e]
  simp only [trapSeedWeight, trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hsum : (∑ a : Fin s → Bool, (2 : ℝ) ^ s *
      (1 / (2 : ℝ) ^ (2 * s) * (if walshChar e a = 1 then 1 / (2 : ℝ) ^ (2 * s) else 0))) =
      ((characterLevel e 1).card : ℝ) * ((2 : ℝ) ^ s *
        (1 / (2 : ℝ) ^ (2 * s) * (1 / (2 : ℝ) ^ (2 * s)))) := by
    simp [characterLevel, Finset.sum_ite, mul_ite]
  rw [hsum]
  have hc : (2 : ℝ) * ((characterLevel e 1).card : ℝ) = (2 : ℝ) ^ s := by
    exact_mod_cast characterLevel_double_card e he 1 (Or.inl rfl)
  have hc' : ((characterLevel e 1).card : ℝ) = (2 : ℝ) ^ s / 2 := by linarith
  have hpow : (2 : ℝ) ^ (2 * s) = ((2 : ℝ) ^ s) ^ 2 := by rw [two_mul, pow_add, pow_two]
  rw [hc', hpow]
  field_simp

theorem initial_swap_bridge_collision {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) (t : ℝ) :
    collision (probabilityBlend (trapLaw e) (rewireLaw e ∅) t) =
      (1 - t + t ^ 2) / (2 : ℝ) ^ (2 * s) := by
  rw [collision_blend_expansion, trapLaw_collision, rewireLaw_initial_collision e he,
    initial_swap_lawOverlap hs e he]
  ring

theorem initial_swap_bridge_minimum {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) :
    collision (probabilityBlend (trapLaw e) (rewireLaw e ∅) (1 / 2)) =
      3 / (4 * (2 : ℝ) ^ (2 * s)) ∧
    ∀ t : ℝ, 3 / (4 * (2 : ℝ) ^ (2 * s)) ≤
      collision (probabilityBlend (trapLaw e) (rewireLaw e ∅) t) := by
  constructor
  · rw [initial_swap_bridge_collision hs e he]
    ring
  · intro t
    rw [initial_swap_bridge_collision hs e he]
    have hn : 0 ≤ (t - 1 / 2) ^ 2 / (2 : ℝ) ^ (2 * s) := by positivity
    have hid : (1 - t + t ^ 2) / (2 : ℝ) ^ (2 * s) - 3 / (4 * (2 : ℝ) ^ (2 * s)) =
        (t - 1 / 2) ^ 2 / (2 : ℝ) ^ (2 * s) := by ring
    linarith

end EntropyDesigns
