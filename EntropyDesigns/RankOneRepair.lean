module

public import EntropyDesigns.LinearUniformLaw
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Rank control for an actual linear repair with one-dimensional difference -/

@[expose] public section
namespace EntropyDesigns

def rankOneRepair {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : W) (f : W →ₗ[ZMod 2] ZMod 2) : W →ₗ[ZMod 2] W := LinearMap.id - f.smulRight v

theorem rankOneRepair_apply {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : W) (f : W →ₗ[ZMod 2] ZMod 2) (x : W) : rankOneRepair v f x = x - f x • v := rfl

theorem rankOneRepair_rank_bounds {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.range ((rankOneRepair v f).comp L)) ≤
      Module.finrank (ZMod 2) (LinearMap.range L) ∧
    Module.finrank (ZMod 2) (LinearMap.range L) ≤
      Module.finrank (ZMod 2) (LinearMap.range ((rankOneRepair v f).comp L)) + 1 := by
  let M := (rankOneRepair v f).comp L
  have hk : LinearMap.ker L ≤ LinearMap.ker M := by
    intro x hx
    change rankOneRepair v f (L x) = 0
    rw [show L x = 0 from hx, map_zero]
  have hdim := Submodule.finrank_mono hk
  have hL := L.finrank_range_add_finrank_ker
  have hM := M.finrank_range_add_finrank_ker
  refine ⟨by change Module.finrank (ZMod 2) M.range ≤ _; omega, ?_⟩
  have hsub : LinearMap.range L ≤ LinearMap.range M ⊔ Submodule.span (ZMod 2) ({v} : Set W) := by
    rintro y ⟨x, rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨M x, ⟨x, rfl⟩, f (L x) • v, ?_, ?_⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · change (L x - f (L x) • v) + f (L x) • v = L x
      exact sub_add_cancel _ _
  have hle := Submodule.finrank_mono hsub
  have hsup := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.range M) (Submodule.span (ZMod 2) ({v} : Set W))
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v} : Set W)) ≤ 1 :=
    finrank_span_le_card ({v} : Set W)
  change Module.finrank (ZMod 2) L.range ≤ Module.finrank (ZMod 2) M.range + 1
  omega

theorem rankOneRepair_rank_dichotomy {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.range L) =
      Module.finrank (ZMod 2) (LinearMap.range ((rankOneRepair v f).comp L)) ∨
    Module.finrank (ZMod 2) (LinearMap.range L) =
      Module.finrank (ZMod 2) (LinearMap.range ((rankOneRepair v f).comp L)) + 1 := by
  have h := rankOneRepair_rank_bounds L v f
  omega

end EntropyDesigns
