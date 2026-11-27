module

public import EntropyDesigns.BinaryObservables
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Finiteness

/-! # Exact pushforward laws of finite binary linear observations -/

@[expose] public section
namespace EntropyDesigns

noncomputable def linearSeedWeight {V : Type*} [Fintype V] (_ : V) : ℝ :=
  1 / (Fintype.card V : ℝ)

noncomputable def linearLaw {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) : W → ℝ := by
  classical
  exact pushLaw L linearSeedWeight

theorem linear_fiber_card {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (a : V) :
    Nat.card {x : V // L x = L a} = Nat.card (LinearMap.ker L) := by
  classical
  exact Nat.card_congr (L.toAddMonoidHom.fiberEquivKer a)

theorem linear_kernel_range_card {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) :
    Nat.card (LinearMap.ker L) * Nat.card (LinearMap.range L) = Fintype.card V := by
  classical
  have hk : Nat.card (LinearMap.ker L) = Nat.card L.toAddMonoidHom.ker :=
    Nat.card_congr {
      toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hr : Nat.card (LinearMap.range L) = Nat.card L.toAddMonoidHom.range :=
    Nat.card_congr {
      toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hk, hr]
  exact (AddSubgroup.card_ker_mul_card_range L.toAddMonoidHom).trans Nat.card_eq_fintype_card

theorem linearLaw_at_image {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (a : V) :
    linearLaw L (L a) = 1 / (Nat.card (LinearMap.range L) : ℝ) := by
  classical
  have hsum : linearLaw L (L a) =
      (Nat.card {x : V // L x = L a} : ℝ) / (Fintype.card V : ℝ) := by
    simp [linearLaw, pushLaw, linearSeedWeight, Finset.sum_ite, Fintype.card_subtype,
      Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, Nat.card_eq_fintype_card]
  rw [hsum, linear_fiber_card]
  have hc : (Nat.card (LinearMap.ker L) : ℝ) *
      (Nat.card (LinearMap.range L) : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast linear_kernel_range_card L
  have hV : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hR : (Nat.card (LinearMap.range L) : ℝ) ≠ 0 := by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hV hR).mpr
  simpa using hc

theorem linearLaw_outside_range {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (y : W) (hy : y ∉ LinearMap.range L) : linearLaw L y = 0 := by
  classical
  have hn : ∀ x, L x ≠ y := by
    intro x hx
    exact hy ⟨x, hx⟩
  simp [linearLaw, pushLaw, hn]

theorem linearLaw_probability {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) : (∀ y, 0 ≤ linearLaw L y) ∧ (∑ y, linearLaw L y) = 1 := by
  classical
  refine ⟨pushLaw_nonneg _ _ (fun _ => by unfold linearSeedWeight; positivity), ?_⟩
  change (∑ y, pushLaw L linearSeedWeight y) = 1
  rw [pushLaw_mass]
  simp [linearSeedWeight, Finset.sum_const, nsmul_eq_mul]

theorem linearLaw_weights {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (y : W) :
    linearLaw L y = 0 ∨ linearLaw L y = 1 / (Nat.card (LinearMap.range L) : ℝ) := by
  classical
  by_cases hy : y ∈ LinearMap.range L
  · obtain ⟨a, rfl⟩ := hy
    exact Or.inr (linearLaw_at_image L a)
  · exact Or.inl (linearLaw_outside_range L y hy)

theorem linearLaw_collision {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) :
    collision (linearLaw L) = 1 / (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range L) := by
  classical
  let : Fintype (LinearMap.range L) := Fintype.ofFinite _
  have hpos : (0 : ℝ) < Nat.card (LinearMap.range L) := by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_pos
  have hc := (entropy_of_uniform_weights (linearLaw L) hpos
    (linearLaw_probability L).2 (linearLaw_weights L)).1
  have hcard : Nat.card (LinearMap.range L) = 2 ^ Module.finrank (ZMod 2) (LinearMap.range L) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range L))
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using hc

theorem linearLaw_support_card {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) :
    (Finset.univ.filter (fun y => linearLaw L y ≠ 0)).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range L) := by
  classical
  let : Fintype (LinearMap.range L) := Fintype.ofFinite _
  have hcard : Nat.card (LinearMap.range L) = 2 ^ Module.finrank (ZMod 2) (LinearMap.range L) := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card] using
      (Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range L))
  apply support_card_of_uniform_weights _ (2 ^ Module.finrank (ZMod 2) (LinearMap.range L))
    (by positivity) (linearLaw_probability L).2
  intro y
  simpa only [hcard, Nat.cast_pow, Nat.cast_ofNat] using linearLaw_weights L y

theorem linearLaw_collision_antitone_rank {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L M : V →ₗ[ZMod 2] W)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range M) ≤
      Module.finrank (ZMod 2) (LinearMap.range L)) : collision (linearLaw L) ≤ collision (linearLaw M) := by
  rw [linearLaw_collision, linearLaw_collision]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_right₀ (by norm_num) hrank

theorem linearLaw_single_rank_step {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L M : V →ₗ[ZMod 2] W)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range L) =
      Module.finrank (ZMod 2) (LinearMap.range M) ∨
      Module.finrank (ZMod 2) (LinearMap.range L) =
        Module.finrank (ZMod 2) (LinearMap.range M) + 1) :
    (collision (linearLaw M) = collision (linearLaw L) ∧
      (Finset.univ.filter (fun y => linearLaw M y ≠ 0)).card =
        (Finset.univ.filter (fun y => linearLaw L y ≠ 0)).card) ∨
    (collision (linearLaw M) = 2 * collision (linearLaw L) ∧
      2 * (Finset.univ.filter (fun y => linearLaw M y ≠ 0)).card =
        (Finset.univ.filter (fun y => linearLaw L y ≠ 0)).card) := by
  classical
  simp only [linearLaw_collision, linearLaw_support_card]
  rcases hrank with h | h
  · left; rw [h]; exact ⟨rfl, rfl⟩
  · right
    rw [h, pow_succ, pow_succ]
    constructor
    · field_simp
    · omega

end EntropyDesigns
