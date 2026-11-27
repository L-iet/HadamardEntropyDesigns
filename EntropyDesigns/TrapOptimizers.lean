module

public import EntropyDesigns.TrapBridge
public import EntropyDesigns.ObservedTrapFrame

/-! # Actual global collision optimizers and their intersection with the trap -/

@[expose] public section
namespace EntropyDesigns

def observedFeasible {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ (∑ x, w x) = 1 ∧
    (∀ j, ∑ x, w x * (bitSign (x j) : ℝ) = 0) ∧
    (∀ i j, i ≠ j → ∑ x, w x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ) = 0)

theorem observed_law_atom_cap {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ)
    (hw : observedFeasible w) : ∀ x, w x ≤ 1 / (2 * (2 : ℝ) ^ s) := by
  have h := finite_frame_atom_cap (@observedFrame s) w observedFrame_sign hw.1
    (observedFrame_isotropic w hw.2.1 hw.2.2.1 hw.2.2.2)
  simpa only [observed_frame_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

theorem observed_law_collision_cap {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ)
    (hw : observedFeasible w) : collision w ≤ 1 / (2 * (2 : ℝ) ^ s) :=
  collision_le_of_atom_bound w _ hw.1 hw.2.1 (observed_law_atom_cap w hw)

theorem endpointLaw_global_maximum (s : ℕ) :
    observedFeasible (endpointLaw s) ∧
    ∀ w : (TrapCoordinate s → Bool) → ℝ, observedFeasible w →
      collision w ≤ collision (endpointLaw s) := by
  refine ⟨⟨(endpointLaw_probability s).1, (endpointLaw_probability s).2,
    endpointLaw_mean, endpointLaw_pair⟩, ?_⟩
  intro w hw
  rw [endpointLaw_collision]
  exact observed_law_collision_cap w hw

theorem observed_optimizer_uniform {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ)
    (hw : observedFeasible w) (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) :
    ∀ x, w x = 0 ∨ w x = 1 / (2 * (2 : ℝ) ^ s) :=
  equality_forces_capped_weights w _ hw.1 hw.2.1 (observed_law_atom_cap w hw) heq

theorem observed_optimizer_orthogonal {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ)
    (hw : observedFeasible w) (heq : collision w = 1 / (2 * (2 : ℝ) ^ s))
    (x y : TrapCoordinate s → Bool) (hx : w x ≠ 0) (hy : w y ≠ 0) (hxy : x ≠ y) :
    inner (@observedFrame s) x y = 0 := by
  have heq' : collision w = 1 / (Fintype.card (Finset (Fin s) ⊕ Finset (Fin s)) : ℝ) := by
    simpa only [observed_frame_card, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using heq
  exact finite_frame_equality_orthogonal observedFrame w observedFrame_sign hw.1 hw.2.1
    (observedFrame_isotropic w hw.2.1 hw.2.2.1 hw.2.2.2) heq' x y hx hy hxy

noncomputable def commonTrapSeeds {s : ℕ} (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) : Finset ((Fin s → Bool) × (Fin s → Bool)) := by
  classical
  exact Finset.univ.filter (fun u => w (trapCode e u) ≠ 0)

theorem optimizer_common_trap_seeds_bound {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w)
    (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) : (commonTrapSeeds e w).card ≤ 2 ^ s := by
  classical
  apply trap_clique_card_le hs e
  intro u hu v hv huv
  have hune : w (trapCode e u) ≠ 0 := (Finset.mem_filter.mp hu).2
  have hvne : w (trapCode e v) ≠ 0 := (Finset.mem_filter.mp hv).2
  have hcode : trapCode e u ≠ trapCode e v := fun h => huv (trapCode_injective e h)
  have h := observed_optimizer_orthogonal w hw heq _ _ hune hvne hcode
  unfold inner at h
  simp_rw [observedFrame_trapCode] at h
  unfold trapInner
  exact_mod_cast h

theorem trapLaw_nonzero_iff {s : ℕ} (e : Finset (Fin s)) (x : TrapCoordinate s → Bool) :
    trapLaw e x ≠ 0 ↔ ∃ u : (Fin s → Bool) × (Fin s → Bool), trapCode e u = x := by
  classical
  constructor
  · intro hx
    by_contra hnot
    have hn : ∀ u : (Fin s → Bool) × (Fin s → Bool), trapCode e u ≠ x := by
      intro u hu; exact hnot ⟨u, hu⟩
    have hz : trapLaw e x = 0 := by simp [trapLaw, pushLaw, hn]
    exact hx hz
  · rintro ⟨u, rfl⟩
    change pushLaw (trapCode e) trapSeedWeight (trapCode e u) ≠ 0
    rw [pushLaw_injective_value _ (trapCode_injective e)]
    simp only [trapSeedWeight, trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
    positivity

theorem optimizer_common_trap_atoms_bound {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w)
    (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) :
    (Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ w x ≠ 0)).card ≤ 2 ^ s := by
  classical
  have hset : Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ w x ≠ 0) =
      (commonTrapSeeds e w).image (trapCode e) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hmu, hwx⟩
      obtain ⟨u, rfl⟩ := (trapLaw_nonzero_iff e x).mp hmu
      exact ⟨u, by simpa [commonTrapSeeds] using hwx, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(trapLaw_nonzero_iff e _).mpr ⟨u, rfl⟩, (Finset.mem_filter.mp hu).2⟩
  rw [hset, Finset.card_image_of_injective _ (trapCode_injective e)]
  exact optimizer_common_trap_seeds_bound hs e w hw heq

theorem optimizer_trap_lawOverlap_bound {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w)
    (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) :
    lawOverlap (trapLaw e) w ≤ 1 / (2 * (2 : ℝ) ^ (2 * s)) := by
  classical
  have huniform := observed_optimizer_uniform w hw heq
  have hsum : (∑ u : (Fin s → Bool) × (Fin s → Bool), w (trapCode e u)) =
      ((commonTrapSeeds e w).card : ℝ) / (2 * (2 : ℝ) ^ s) := by
    calc
      _ = ∑ u ∈ commonTrapSeeds e w, 1 / (2 * (2 : ℝ) ^ s) := by
        rw [commonTrapSeeds, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hz : w (trapCode e u) = 0
        · simp [hz]
        · simp [(huniform _).resolve_left hz]
      _ = _ := by simp [div_eq_mul_inv]
  have hdot : lawOverlap (trapLaw e) w =
      (1 / (2 : ℝ) ^ (2 * s)) *
        (((commonTrapSeeds e w).card : ℝ) / (2 * (2 : ℝ) ^ s)) := by
    unfold lawOverlap trapLaw
    rw [pushLaw_moment]
    simp only [trapSeedWeight, trap_seed_card, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum, hsum]
  have hc : ((commonTrapSeeds e w).card : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast optimizer_common_trap_seeds_bound hs e w hw heq
  rw [hdot]
  calc
    _ ≤ (1 / (2 : ℝ) ^ (2 * s)) * ((2 : ℝ) ^ s / (2 * (2 : ℝ) ^ s)) := by
      gcongr
    _ = _ := by field_simp

theorem optimizer_bridge_comparison {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w)
    (heq : collision w = 1 / (2 * (2 : ℝ) ^ s))
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    collision (probabilityBlend (trapLaw e) w t) ≤
      collision (probabilityBlend (trapLaw e) (endpointLaw s) t) := by
  have hc := optimizer_trap_lawOverlap_bound hs e w hw heq
  have hnu := trap_endpoint_lawOverlap hs e
  have hd : collision (probabilityBlend (trapLaw e) (endpointLaw s) t) -
      collision (probabilityBlend (trapLaw e) w t) =
      2 * t * (1 - t) * (lawOverlap (trapLaw e) (endpointLaw s) - lawOverlap (trapLaw e) w) := by
    rw [collision_blend_expansion, collision_blend_expansion, endpointLaw_collision, heq]
    ring
  have hn : 0 ≤ 2 * t * (1 - t) *
      (lawOverlap (trapLaw e) (endpointLaw s) - lawOverlap (trapLaw e) w) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) ht) (sub_nonneg.mpr ht')
    · rw [hnu]
      exact sub_nonneg.mpr hc
  linarith

theorem trap_bridge_optimal_among_global_maximizers {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w)
    (hmax : ∀ q : (TrapCoordinate s → Bool) → ℝ, observedFeasible q → collision q ≤ collision w) :
    (Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ w x ≠ 0)).card ≤ 2 ^ s ∧
    collision (probabilityBlend (trapLaw e) w (1 / (2 : ℝ) ^ s)) ≤
      (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) := by
  have heq : collision w = 1 / (2 * (2 : ℝ) ^ s) := by
    apply le_antisymm (observed_law_collision_cap w hw)
    have h := hmax (endpointLaw s) (endpointLaw_global_maximum s).1
    rwa [endpointLaw_collision] at h
  refine ⟨optimizer_common_trap_atoms_bound hs e w hw heq, ?_⟩
  have ht := (trap_bridge_minimum hs e).1
  have hc := optimizer_bridge_comparison hs e w hw heq _ ht.1 ht.2
  rwa [(trap_bridge_minimum hs e).2.1] at hc

end EntropyDesigns
