module

public import EntropyDesigns.RewiringSchedule
public import EntropyDesigns.LinearUniformLaw

/-! # Boolean character laws are the actual laws of binary linear encoders -/

@[expose] public section
namespace EntropyDesigns

noncomputable local instance {s : ℕ} : DecidableEq (TrapCoordinate s → ZMod 2) := Classical.decEq _

def fieldCode {ι : Type*} (z : ι → ZMod 2) : ι → Bool := fun i => decide (z i = 1)

theorem fieldCode_bijective {ι : Type*} : Function.Bijective (@fieldCode ι) := by
  constructor
  · intro x y h
    funext i
    have hi := congrFun h i
    rcases binaryField_cases (x i) with hx | hx <;>
      rcases binaryField_cases (y i) with hy | hy <;> simp_all [fieldCode]
  · intro x
    refine ⟨fun i => if x i then 1 else 0, ?_⟩
    funext i
    cases hx : x i <;> simp [fieldCode, hx]

def pairedBinarySeed {s : ℕ} (u : (Fin s → Bool) × (Fin s → Bool)) :
    (Fin s → ZMod 2) × (Fin s → ZMod 2) := (binarySeed u.1, binarySeed u.2)

theorem pairedBinarySeed_bijective {s : ℕ} : Function.Bijective (@pairedBinarySeed s) := by
  constructor
  · intro u v h
    exact Prod.ext (binarySeed_bijective.1 (congrArg Prod.fst h))
      (binarySeed_bijective.1 (congrArg Prod.snd h))
  · rintro ⟨x, y⟩
    obtain ⟨a, ha⟩ := binarySeed_bijective.2 x
    obtain ⟨b, hb⟩ := binarySeed_bijective.2 y
    exact ⟨(a, b), Prod.ext ha hb⟩

def maskPairLinear {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    ((Fin s → ZMod 2) × (Fin s → ZMod 2)) →ₗ[ZMod 2] (TrapCoordinate s → ZMod 2) where
  toFun z j := maskFunctional (M j.val).1 z.1 + maskFunctional (M j.val).2 z.2
  map_add' x y := by
    funext j
    change maskFunctional (M j.val).1 (x.1 + y.1) + maskFunctional (M j.val).2 (x.2 + y.2) = _
    rw [map_add, map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext j
    change maskFunctional (M j.val).1 (a • x.1) + maskFunctional (M j.val).2 (a • x.2) = _
    simp [map_smul, mul_add]

theorem maskPairCode_linear {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) :
    maskPairCode M u = fieldCode (maskPairLinear M (pairedBinarySeed u)) := by
  funext j
  apply bitSign_injective
  rw [maskPairCode_sign]
  unfold maskPairRow
  rw [walshChar_binaryFunctional, walshChar_binaryFunctional]
  rcases binaryField_cases (maskFunctional (M j.val).1 (binarySeed u.1)) with h1 | h1 <;>
    rcases binaryField_cases (maskFunctional (M j.val).2 (binarySeed u.2)) with h2 | h2 <;>
    norm_num [fieldCode, maskPairLinear, pairedBinarySeed, bitSign, h1, h2,
      show (1 : ZMod 2) + 1 = 0 by decide]

theorem pairedBinarySeed_uniform {s : ℕ} :
    pushLaw (@pairedBinarySeed s) trapSeedWeight = linearSeedWeight := by
  classical
  have hc := Fintype.card_congr (Equiv.ofBijective (@pairedBinarySeed s) pairedBinarySeed_bijective)
  funext z
  obtain ⟨u, rfl⟩ := pairedBinarySeed_bijective.2 z
  rw [pushLaw_injective_value _ pairedBinarySeed_bijective.1]
  simp only [trapSeedWeight, linearSeedWeight, hc]

theorem maskPairLaw_linear {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    maskPairLaw M = pushLaw (@fieldCode (TrapCoordinate s)) (linearLaw (maskPairLinear M)) := by
  classical
  let E := Equiv.ofBijective (@pairedBinarySeed s) pairedBinarySeed_bijective
  have hc := Fintype.card_congr E
  funext x
  have hsum : maskPairLaw M x =
      pushLaw ((@fieldCode (TrapCoordinate s)) ∘ maskPairLinear M) linearSeedWeight x := by
    unfold maskPairLaw pushLaw
    simp only [Function.comp_apply]
    rw [← E.sum_comp (fun z => if fieldCode (maskPairLinear M z) = x then linearSeedWeight z else 0)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [maskPairCode_linear]
    simp only [E, Equiv.ofBijective_apply, linearSeedWeight, trapSeedWeight, hc]
  rw [hsum]
  unfold linearLaw
  exact (pushLaw_comp (maskPairLinear M) (@fieldCode (TrapCoordinate s)) linearSeedWeight x).symm

theorem maskPairLaw_rank_collision {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    collision (maskPairLaw M) =
      1 / (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear M)) := by
  classical
  rw [maskPairLaw_linear, pushLaw_injective_collision _ fieldCode_bijective.1, linearLaw_collision]

theorem maskPairLaw_rank_weights {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    ∀ x, maskPairLaw M x = 0 ∨ maskPairLaw M x =
      1 / (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear M)) := by
  classical
  let : Fintype (LinearMap.range (maskPairLinear M)) := Fintype.ofFinite _
  have hc : Nat.card (LinearMap.range (maskPairLinear M)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear M)) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range (maskPairLinear M)))
  intro x
  obtain ⟨z, rfl⟩ := fieldCode_bijective.2 x
  rw [maskPairLaw_linear, pushLaw_injective_value _ fieldCode_bijective.1]
  simpa only [hc, Nat.cast_pow, Nat.cast_ofNat] using linearLaw_weights (maskPairLinear M) z

theorem maskPairLaw_rank_support {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    (Finset.univ.filter (fun x => maskPairLaw M x ≠ 0)).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear M)) := by
  classical
  have hm : (∑ x, maskPairLaw M x) = 1 := (pushLaw_mass _ _).trans (trapSeedWeight_mass s)
  apply support_card_of_uniform_weights _ _ (by positivity) hm
  intro x
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using maskPairLaw_rank_weights M x

end EntropyDesigns
