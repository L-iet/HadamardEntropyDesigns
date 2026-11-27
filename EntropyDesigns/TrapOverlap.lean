module

public import EntropyDesigns.TrapEndpoint
public import EntropyDesigns.TrapCliques
public import EntropyDesigns.StraightBridge

/-! # Exact identification of the shared trap and endpoint atoms -/

@[expose] public section
namespace EntropyDesigns

theorem nonempty_characters_not_all_negated {s : ℕ} (hs : 2 ≤ s)
    (a b : Fin s → Bool) :
    ¬ (∀ S : Finset (Fin s), S ≠ ∅ → walshChar S b = -walshChar S a) := by
  intro h
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  have hij : i ≠ j := by intro he; have hv := congrArg Fin.val he; dsimp [i, j] at hv; omega
  have h1 := h {i} (by simp)
  have h2 := h {j} (by simp)
  have h3 := h {i, j} (by simp)
  simp only [walshChar_singleton] at h1 h2
  rw [walshChar_pair i j hij, walshChar_pair i j hij, h1, h2] at h3
  rcases bitSign_sign (a i) with hi | hi <;> rcases bitSign_sign (a j) with hj | hj <;>
    norm_num [hi, hj] at h3

theorem trap_endpoint_code_eq_iff {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (a b c : Fin s → Bool) (t : Bool) :
    trapCode e (a, b) = endpointCode (c, t) ↔ a = c ∧ b = c ∧ t = false := by
  constructor
  · intro hcode
    have hrow : ∀ j, trapRow e (a, b) j = endpointRow (c, t) j := by
      intro j
      by_cases hj : j = Sum.inl ∅
      · subst j; simp [trapRow, endpointRow, walshChar]
      · simpa only [trapCode_sign, endpointCode_sign] using
          congrArg (fun x => bitSign (x ⟨j, hj⟩)) hcode
    have hac : a = c := walsh_characters_separate a c (fun S => hrow (Sum.inl S))
    have hright : ∀ S : Finset (Fin s), S ≠ ∅ →
        walshChar S b = bitSign t * walshChar S c := by
      intro S hS
      simpa [trapRow, endpointRow, hS] using hrow (Sum.inr S)
    have ht : t = false := by
      cases t
      · rfl
      · exfalso
        apply nonempty_characters_not_all_negated hs c b
        intro S hS
        simpa [bitSign] using hright S hS
    have hbc : b = c := by
      apply walsh_characters_separate
      intro S
      by_cases hS : S = ∅
      · simp [hS, walshChar]
      · simpa [ht, bitSign] using hright S hS
    exact ⟨hac, hbc, ht⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext j
    apply bitSign_injective
    rw [trapCode_sign, endpointCode_sign]
    rcases j with ⟨j, hj⟩
    cases j with
    | inl S => rfl
    | inr S =>
      by_cases hS : S = ∅
      · simp [trapRow, endpointRow, hS, bitSign, trapMixed_diagonal, walshChar]
      · simp [trapRow, endpointRow, hS, bitSign]

theorem trapLaw_at_endpoint {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (c : Fin s → Bool) (t : Bool) :
    trapLaw e (endpointCode (c, t)) = if t = false then 1 / (2 : ℝ) ^ (2 * s) else 0 := by
  classical
  cases t
  · have heq : trapCode e (c, c) = endpointCode (c, false) :=
      (trap_endpoint_code_eq_iff hs e c c c false).mpr ⟨rfl, rfl, rfl⟩
    change pushLaw (trapCode e) trapSeedWeight (endpointCode (c, false)) = _
    rw [← heq, pushLaw_injective_value _ (trapCode_injective e)]
    simp only [trapSeedWeight, trap_seed_card, Nat.cast_pow, Nat.cast_ofNat, ite_true]
  · change (∑ u, if trapCode e u = endpointCode (c, true) then trapSeedWeight u else 0) = _
    have hn : ∀ u : (Fin s → Bool) × (Fin s → Bool), trapCode e u ≠ endpointCode (c, true) := by
      rintro ⟨a, b⟩ h
      have hh := ((trap_endpoint_code_eq_iff hs e a b c true).mp h).2.2
      cases hh
    simp [hn]

theorem trap_endpoint_lawOverlap {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) :
    lawOverlap (trapLaw e) (endpointLaw s) = 1 / (2 * (2 : ℝ) ^ (2 * s)) := by
  classical
  have hpush := pushLaw_moment endpointCode (@endpointSeedWeight s) (trapLaw e)
  have hsum : lawOverlap (trapLaw e) (endpointLaw s) =
      ∑ u : (Fin s → Bool) × Bool, endpointSeedWeight u * trapLaw e (endpointCode u) := by
    unfold lawOverlap
    rw [← hpush]
    apply Finset.sum_congr rfl
    intro x hx
    unfold endpointLaw
    ring
  rw [hsum, Fintype.sum_prod_type]
  have hbool : ∀ a : Fin s → Bool,
      (∑ t : Bool, endpointSeedWeight (a, t) * trapLaw e (endpointCode (a, t))) =
        (1 / (2 * (2 : ℝ) ^ s)) * (1 / (2 : ℝ) ^ (2 * s)) := by
    intro a
    have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
    rw [huniv]
    simp only [trapLaw_at_endpoint hs e]
    simp [endpointSeedWeight, mul_comm]
  simp_rw [hbool]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem endpointLaw_nonzero_iff {s : ℕ} (x : TrapCoordinate s → Bool) :
    endpointLaw s x ≠ 0 ↔ ∃ u : (Fin s → Bool) × Bool, endpointCode u = x := by
  classical
  constructor
  · intro hx
    by_contra hnot
    have hn : ∀ u : (Fin s → Bool) × Bool, endpointCode u ≠ x := by
      intro u hu; exact hnot ⟨u, hu⟩
    have hz : endpointLaw s x = 0 := by simp [endpointLaw, pushLaw, hn]
    exact hx hz
  · rintro ⟨u, rfl⟩
    change pushLaw endpointCode endpointSeedWeight (endpointCode u) ≠ 0
    rw [pushLaw_injective_value _ endpointCode_injective]
    simp only [endpointSeedWeight, endpoint_seed_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    positivity

theorem trap_endpoint_common_atoms {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) :
    (Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ endpointLaw s x ≠ 0)).card = 2 ^ s := by
  classical
  have hset : Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ endpointLaw s x ≠ 0) =
      Finset.univ.image (fun a : Fin s → Bool => endpointCode (a, false)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hmu, hnu⟩
      obtain ⟨⟨a, t⟩, rfl⟩ := endpointLaw_nonzero_iff x |>.mp hnu
      rw [trapLaw_at_endpoint hs e] at hmu
      cases t
      · exact ⟨a, rfl⟩
      · simp at hmu
    · rintro ⟨a, rfl⟩
      constructor
      · rw [trapLaw_at_endpoint hs e]
        simp
      · exact endpointLaw_nonzero_iff _ |>.mpr ⟨(a, false), rfl⟩
  have hinj : Function.Injective (fun a : Fin s → Bool => endpointCode (a, false)) := by
    intro a b h
    exact congrArg Prod.fst (endpointCode_injective h)
  rw [hset, Finset.card_image_of_injective _ hinj]
  simp

end EntropyDesigns
