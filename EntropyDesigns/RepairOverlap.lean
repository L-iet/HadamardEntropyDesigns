module

public import EntropyDesigns.LinearOverlap
public import EntropyDesigns.RankOneRepair

/-! # Exact cross inner products under a one-dimensional repair -/

@[expose] public section
namespace EntropyDesigns

theorem rankOneRepair_range_sup {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2)
    (hex : ∃ x, f (L x) = 1) :
    LinearMap.range L ⊔ LinearMap.range ((rankOneRepair v f).comp L) =
      LinearMap.range L ⊔ Submodule.span (ZMod 2) ({v} : Set W) := by
  let M := (rankOneRepair v f).comp L
  apply le_antisymm
  · apply sup_le le_sup_left
    rintro y ⟨x, rfl⟩
    change L x - f (L x) • v ∈ _
    apply Submodule.sub_mem
    · exact Submodule.mem_sup_left ⟨x, rfl⟩
    · apply Submodule.mem_sup_right
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    intro y hy
    have hyv : y = v := Set.mem_singleton_iff.mp hy
    subst y
    obtain ⟨x, hx⟩ := hex
    have hdiff : L x - M x = v := by
      change L x - (L x - f (L x) • v) = v
      rw [hx, one_smul]
      abel
    have hmem : L x - M x ∈ LinearMap.range L ⊔ LinearMap.range M :=
      Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ⟨x, rfl⟩)
    exact Eq.mp (congrArg (fun y : W => y ∈ LinearMap.range L ⊔ LinearMap.range M) hdiff) hmem

theorem rankOneRepair_rank_by_membership {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2) (hfv : f v = 1) :
    (v ∈ LinearMap.range L → Module.finrank (ZMod 2) L.range =
      Module.finrank (ZMod 2) (LinearMap.range ((rankOneRepair v f).comp L)) + 1) ∧
    (v ∉ LinearMap.range L → Module.finrank (ZMod 2) L.range =
      Module.finrank (ZMod 2) (LinearMap.range ((rankOneRepair v f).comp L))) := by
  let M := (rankOneRepair v f).comp L
  have hk : LinearMap.ker L ≤ LinearMap.ker M := by
    intro x hx
    change rankOneRepair v f (L x) = 0
    rw [show L x = 0 from hx, map_zero]
  have hL := L.finrank_range_add_finrank_ker
  have hM := M.finrank_range_add_finrank_ker
  constructor
  · rintro ⟨x, hx⟩
    have hv0 : v ≠ 0 := by intro h; rw [h, map_zero] at hfv; norm_num at hfv
    have hnot : ¬LinearMap.ker M ≤ LinearMap.ker L := by
      intro hle
      have hxM : x ∈ LinearMap.ker M := by
        change rankOneRepair v f (L x) = 0
        rw [hx, rankOneRepair_apply, hfv, one_smul, sub_self]
      have hxL : L x = 0 := hle hxM
      rw [hx] at hxL
      exact hv0 hxL
    have hstrict := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hk hnot)
    have hb := rankOneRepair_rank_bounds L v f
    change Module.finrank (ZMod 2) M.range ≤ Module.finrank (ZMod 2) L.range ∧
      Module.finrank (ZMod 2) L.range ≤ Module.finrank (ZMod 2) M.range + 1 at hb
    change Module.finrank (ZMod 2) L.range = Module.finrank (ZMod 2) M.range + 1
    omega
  · intro hv
    have heq : LinearMap.ker M = LinearMap.ker L := by
      apply le_antisymm ?_ hk
      intro x hx
      have hz : L x - f (L x) • v = 0 := hx
      have he : L x = f (L x) • v := sub_eq_zero.mp hz
      rcases binaryField_cases (f (L x)) with h | h
      · change L x = 0
        simpa only [h, zero_smul] using he
      · have hxv : L x = v := by simpa only [h, one_smul] using he
        exact False.elim (hv ⟨x, hxv⟩)
    rw [heq] at hM
    change Module.finrank (ZMod 2) L.range = Module.finrank (ZMod 2) M.range
    omega

theorem rankOneRepair_lawOverlap {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2)
    (hex : ∃ x, f (L x) = 1) :
    (v ∈ LinearMap.range L → lawOverlap (linearLaw L) (linearLaw ((rankOneRepair v f).comp L)) =
      collision (linearLaw L)) ∧
    (v ∉ LinearMap.range L → lawOverlap (linearLaw L) (linearLaw ((rankOneRepair v f).comp L)) =
      collision (linearLaw L) / 2) := by
  classical
  simp only [linear_lawOverlap_rank, linearLaw_collision]
  have hdim := congrArg (fun S : Submodule (ZMod 2) W => Module.finrank (ZMod 2) S)
    (rankOneRepair_range_sup L v f hex)
  simp_rw [hdim]
  constructor
  · intro hv
    have hs : Submodule.span (ZMod 2) ({v} : Set W) ≤ LinearMap.range L := by
      apply Submodule.span_le.mpr
      intro x hx
      change x ∈ LinearMap.range L
      rw [Set.mem_singleton_iff.mp hx]
      exact hv
    exact congrArg (fun S : Submodule (ZMod 2) W => 1 / (2 : ℝ) ^ Module.finrank (ZMod 2) S)
      (sup_eq_left.mpr hs)
  · intro hv
    rw [Submodule.finrank_sup_span_singleton hv, pow_succ]
    field_simp

theorem rankOneRepair_collision_by_membership {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2) (hfv : f v = 1) :
    (v ∈ L.range → collision (linearLaw ((rankOneRepair v f).comp L)) = 2 * collision (linearLaw L)) ∧
    (v ∉ L.range → collision (linearLaw ((rankOneRepair v f).comp L)) = collision (linearLaw L)) := by
  have hr := rankOneRepair_rank_by_membership L v f hfv
  constructor
  · intro hv
    rw [linearLaw_collision, linearLaw_collision, hr.1 hv, pow_succ]
    field_simp
  · intro hv
    rw [linearLaw_collision, linearLaw_collision, hr.2 hv]

theorem rankOneRepair_bridge_polynomial {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2) (hfv : f v = 1)
    (hex : ∃ x, f (L x) = 1) (t : ℝ) :
    (v ∈ L.range → collision (probabilityBlend (linearLaw L) (linearLaw ((rankOneRepair v f).comp L)) t) =
      collision (linearLaw L) * (1 + t ^ 2)) ∧
    (v ∉ L.range → collision (probabilityBlend (linearLaw L) (linearLaw ((rankOneRepair v f).comp L)) t) =
      collision (linearLaw L) * (1 - t + t ^ 2)) := by
  have hc := rankOneRepair_collision_by_membership L v f hfv
  have ho := rankOneRepair_lawOverlap L v f hex
  constructor
  · intro hv
    rw [collision_blend_expansion, hc.1 hv, ho.1 hv]
    ring
  · intro hv
    rw [collision_blend_expansion, hc.2 hv, ho.2 hv]
    ring

theorem rankOneRepair_bridge_lower_bound {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) (v : W) (f : W →ₗ[ZMod 2] ZMod 2) (hfv : f v = 1)
    (hex : ∃ x, f (L x) = 1) (t : ℝ) :
    (3 / 4 : ℝ) * collision (linearLaw L) ≤
      collision (probabilityBlend (linearLaw L) (linearLaw ((rankOneRepair v f).comp L)) t) := by
  have hC : 0 ≤ collision (linearLaw L) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp := rankOneRepair_bridge_polynomial L v f hfv hex t
  by_cases hv : v ∈ L.range
  · rw [hp.1 hv]
    nlinarith [mul_nonneg hC (sq_nonneg t)]
  · rw [hp.2 hv]
    nlinarith [mul_nonneg hC (sq_nonneg (t - 1 / 2))]

end EntropyDesigns
