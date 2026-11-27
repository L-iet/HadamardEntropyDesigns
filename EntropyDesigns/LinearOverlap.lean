module

public import EntropyDesigns.LinearUniformLaw
public import EntropyDesigns.StraightBridge

/-! # Cross inner products of actual finite binary linear laws -/

@[expose] public section
namespace EntropyDesigns

def differenceEncoder {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (L M : V →ₗ[ZMod 2] W) :
    (V × V) →ₗ[ZMod 2] W := L.coprod (-M)

theorem differenceEncoder_apply {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (L M : V →ₗ[ZMod 2] W) (u v : V) :
    differenceEncoder L M (u, v) = L u - M v := by
  simp [differenceEncoder, LinearMap.coprod_apply, sub_eq_add_neg]

theorem differenceEncoder_range {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (L M : V →ₗ[ZMod 2] W) :
    LinearMap.range (differenceEncoder L M) = LinearMap.range L ⊔ LinearMap.range M := by
  apply le_antisymm
  · rintro z ⟨⟨u, v⟩, hz⟩
    apply Submodule.mem_sup.mpr
    refine ⟨L u, ⟨u, rfl⟩, -M v, ⟨-v, by simp⟩, ?_⟩
    simpa [differenceEncoder_apply, sub_eq_add_neg] using hz
  · intro z hz
    obtain ⟨a, ⟨u, rfl⟩, b, ⟨v, rfl⟩, hab⟩ := Submodule.mem_sup.mp hz
    refine ⟨(u, -v), ?_⟩
    simpa [differenceEncoder_apply] using hab

theorem lawOverlap_push_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (p q : α → ℝ) :
    lawOverlap (pushLaw f p) (pushLaw f q) = lawOverlap p q := by
  have h := pushLaw_moment f p (pushLaw f q)
  simp only [pushLaw_injective_value f hf q] at h
  exact h

theorem linear_lawOverlap_zero {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L M : V →ₗ[ZMod 2] W) :
    lawOverlap (linearLaw L) (linearLaw M) = linearLaw (differenceEncoder L M) 0 := by
  classical
  have hweight : ∀ u v : V, linearSeedWeight u * linearSeedWeight v = linearSeedWeight (u, v) := by
    intro u v
    simp [linearSeedWeight, Fintype.card_prod, Nat.cast_mul, div_eq_mul_inv]
  calc
    _ = ∑ u : V, linearSeedWeight u * linearLaw M (L u) := by
      exact pushLaw_moment L linearSeedWeight (linearLaw M)
    _ = _ := by
      change (∑ u : V, linearSeedWeight u *
        (∑ v : V, if M v = L u then linearSeedWeight v else 0)) =
        ∑ z : V × V, if differenceEncoder L M z = 0 then linearSeedWeight z else 0
      rw [Fintype.sum_prod_type]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have heq : M v = L u ↔ differenceEncoder L M (u, v) = 0 := by
        rw [differenceEncoder_apply, sub_eq_zero]
        exact eq_comm
      simp only [mul_ite, mul_zero, hweight, heq]

theorem linear_lawOverlap_rank {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L M : V →ₗ[ZMod 2] W) :
    lawOverlap (linearLaw L) (linearLaw M) =
      1 / (2 : ℝ) ^ Module.finrank (ZMod 2) ↥(LinearMap.range L ⊔ LinearMap.range M) := by
  classical
  let F := differenceEncoder L M
  let : Fintype (LinearMap.range F) := Fintype.ofFinite _
  have hz : linearLaw F 0 = 1 / (Nat.card (LinearMap.range F) : ℝ) := by
    simpa only [map_zero] using linearLaw_at_image F (0 : V × V)
  have hc : Nat.card (LinearMap.range F) = 2 ^ Module.finrank (ZMod 2) (LinearMap.range F) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range F))
  rw [linear_lawOverlap_zero]
  change linearLaw F 0 = _
  rw [hz, hc]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show LinearMap.range F = LinearMap.range L ⊔ LinearMap.range M from differenceEncoder_range L M]

theorem pushLaw_blend {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (p q : α → ℝ) (t : ℝ) :
    pushLaw f (probabilityBlend p q t) = probabilityBlend (pushLaw f p) (pushLaw f q) t := by
  funext y
  have hp : ∀ a, (if f a = y then probabilityBlend p q t a else 0) =
      (1 - t) * (if f a = y then p a else 0) + t * (if f a = y then q a else 0) := by
    intro a
    by_cases h : f a = y <;> simp [h, probabilityBlend]
  unfold pushLaw
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

end EntropyDesigns
