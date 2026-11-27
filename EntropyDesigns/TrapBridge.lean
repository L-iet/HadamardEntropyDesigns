module

public import EntropyDesigns.TrapOverlap

/-! # Exact collision and minimum on the explicitly constructed escape bridge -/

@[expose] public section
namespace EntropyDesigns

theorem trap_bridge_collision {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (t : ℝ) :
    collision (probabilityBlend (trapLaw e) (endpointLaw s) t) =
      (1 - t + ((2 : ℝ) ^ s / 2) * t ^ 2) / (2 : ℝ) ^ (2 * s) := by
  rw [collision_blend_expansion, trapLaw_collision, endpointLaw_collision,
    trap_endpoint_lawOverlap hs e]
  have hp : (2 : ℝ) ^ (2 * s) = ((2 : ℝ) ^ s) ^ 2 := by
    rw [two_mul, pow_add, pow_two]
  rw [hp]
  field_simp
  ring

theorem trap_bridge_square_identity {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (t : ℝ) :
    collision (probabilityBlend (trapLaw e) (endpointLaw s) t) -
      (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) =
      (t - 1 / (2 : ℝ) ^ s) ^ 2 / (2 * (2 : ℝ) ^ s) := by
  rw [trap_bridge_collision hs e]
  have hp : (2 : ℝ) ^ (2 * s) = ((2 : ℝ) ^ s) ^ 2 := by
    rw [two_mul, pow_add, pow_two]
  rw [hp]
  field_simp
  ring

theorem trap_bridge_minimum {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) :
    (0 ≤ 1 / (2 : ℝ) ^ s ∧ 1 / (2 : ℝ) ^ s ≤ 1) ∧
    collision (probabilityBlend (trapLaw e) (endpointLaw s) (1 / (2 : ℝ) ^ s)) =
      (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) ∧
    (∀ t : ℝ, (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) ≤
      collision (probabilityBlend (trapLaw e) (endpointLaw s) t)) := by
  have hh : (4 : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast two_pow_ge_four hs
  refine ⟨⟨by positivity, ?_⟩, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ s)).mpr
    linarith
  · have h := trap_bridge_square_identity hs e (1 / (2 : ℝ) ^ s)
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_div] at h
    exact sub_eq_zero.mp h
  · intro t
    have h := trap_bridge_square_identity hs e t
    have hn : 0 ≤ (t - 1 / (2 : ℝ) ^ s) ^ 2 / (2 * (2 : ℝ) ^ s) := by positivity
    linarith

theorem trap_bridge_exact_loss {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) :
    collision (trapLaw e) -
      collision (probabilityBlend (trapLaw e) (endpointLaw s) (1 / (2 : ℝ) ^ s)) =
        1 / (2 * ((2 : ℝ) ^ s) ^ 3) := by
  rw [trapLaw_collision, (trap_bridge_minimum hs e).2.1]
  have hp : (2 : ℝ) ^ (2 * s) = ((2 : ℝ) ^ s) ^ 2 := by
    rw [two_mul, pow_add, pow_two]
  rw [hp]
  field_simp
  ring

theorem trap_bridge_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (∀ x, 0 ≤ probabilityBlend (trapLaw e) (endpointLaw s) t x) ∧
    (∑ x, probabilityBlend (trapLaw e) (endpointLaw s) t x) = 1 ∧
    (∀ j : TrapCoordinate s, ∑ x, probabilityBlend (trapLaw e) (endpointLaw s) t x *
      (bitSign (x j) : ℝ) = 0) ∧
    (∀ i j : TrapCoordinate s, i ≠ j →
      ∑ x, probabilityBlend (trapLaw e) (endpointLaw s) t x *
        (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ) = 0) := by
  classical
  refine ⟨probabilityBlend_nonneg (trapLaw e) (endpointLaw s) t
    (trapLaw_probability e).1 (endpointLaw_probability s).1 ht ht',
    probabilityBlend_mass (trapLaw e) (endpointLaw s) t
      (trapLaw_probability e).2 (endpointLaw_probability s).2, ?_, ?_⟩
  · intro j
    exact probabilityBlend_moment (trapLaw e) (endpointLaw s) (fun x => (bitSign (x j) : ℝ)) t 0
      (trapLaw_mean e he j) (endpointLaw_mean j)
  · intro i j hij
    have hp : (∑ x, trapLaw e x * ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0 := by
      simpa only [mul_assoc] using trapLaw_pair e he i j hij
    have hq : (∑ x, endpointLaw s x * ((bitSign (x i) : ℝ) * (bitSign (x j) : ℝ))) = 0 := by
      simpa only [mul_assoc] using endpointLaw_pair i j hij
    simpa only [mul_assoc] using probabilityBlend_moment (trapLaw e) (endpointLaw s)
      (fun x => (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) t 0 hp hq

end EntropyDesigns
