module

public import EntropyDesigns.StraightBridge

/-! # Collision-increasing feasible support deletion -/

@[expose] public section
namespace EntropyDesigns

theorem lawOverlap_sub {α : Type*} [Fintype α] (p q r : α → ℝ) :
    lawOverlap p (q - r) = lawOverlap p q - lawOverlap p r := by
  simp [lawOverlap, mul_sub, Finset.sum_sub_distrib]

theorem lawOverlap_self {α : Type*} [Fintype α] (p : α → ℝ) :
    lawOverlap p p = collision p := by
  simp [lawOverlap, collision, pow_two]

theorem support_deletion_endpoint {α : Type*} [Fintype α]
    (p z : α → ℝ) (hp : ∀ a, 0 < p a)
    (hneg : ∃ a, z a < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ a, 0 ≤ p a + t * z a) ∧
      (∃ a, p a + t * z a = 0) := by
  classical
  let S := Finset.univ.filter (fun a => z a < 0)
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := hneg
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (fun a => p a / (-z a)) hS
  have hza : z a < 0 := (Finset.mem_filter.mp ha).2
  refine ⟨p a / (-z a), div_pos (hp a) (neg_pos.mpr hza), ?_, ?_⟩
  · intro b
    by_cases hzb : z b < 0
    · have hbound := hmin b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hzb⟩)
      have := (le_div_iff₀ (neg_pos.mpr hzb)).mp hbound
      nlinarith
    · have ht := (div_pos (hp a) (neg_pos.mpr hza)).le
      have := mul_nonneg ht (le_of_not_gt hzb)
      linarith [hp b]
  · refine ⟨a, ?_⟩
    field_simp [ne_of_lt hza]
    ring

theorem collision_direction_expansion {α : Type*} [Fintype α]
    (p z : α → ℝ) (t : ℝ) :
    collision (fun a => p a + t * z a) =
      collision p + 2 * t * lawOverlap p z + t ^ 2 * collision z := by
  have h : ∀ a, (p a + t * z a) ^ 2 =
      p a ^ 2 + (2 * t) * (p a * z a) + t ^ 2 * z a ^ 2 := by
    intro a
    ring
  unfold collision
  simp_rw [h]
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  unfold lawOverlap
  ring

theorem collision_direction_strict_increase {α : Type*} [Fintype α]
    (p z : α → ℝ) (hz : z ≠ 0) (horient : 0 ≤ lawOverlap p z)
    (t : ℝ) (ht : 0 < t) :
    collision p < collision (fun a => p a + t * z a) := by
  have hpos : 0 < collision z := by
    have h := collision_distance_pos z 0 hz
    simpa [collision, lawOverlap] using h
  rw [collision_direction_expansion]
  have hlin : 0 ≤ 2 * t * lawOverlap p z :=
    mul_nonneg (by positivity) horient
  have hquad : 0 < t ^ 2 * collision z := mul_pos (sq_pos_of_pos ht) hpos
  linarith

theorem collision_direction_monotone {α : Type*} [Fintype α]
    (p z : α → ℝ) (horient : 0 ≤ lawOverlap p z) :
    MonotoneOn (fun t : ℝ => collision (fun a => p a + t * z a))
      (Set.Ici 0) := by
  intro s hs t _ hst
  dsimp only
  change 0 ≤ s at hs
  rw [collision_direction_expansion, collision_direction_expansion]
  have hquad : 0 ≤ collision z := Finset.sum_nonneg (fun a _ => sq_nonneg (z a))
  have hsquare : s ^ 2 ≤ t ^ 2 := by nlinarith [hs]
  have h1 := mul_le_mul_of_nonneg_right hst horient
  have h2 := mul_le_mul_of_nonneg_right hsquare hquad
  linarith

theorem kernel_direction_feasible {α ι : Type*} [Fintype α]
    (p z : α → ℝ) (φ : ι → α → ℝ) (k : ι → ℝ)
    (hp : ∑ a, p a = 1) (hz : ∑ a, z a = 0)
    (hmoment : ∀ i, ∑ a, p a * φ i a = k i)
    (hkernel : ∀ i, ∑ a, z a * φ i a = 0) (t : ℝ) :
    (∑ a, (p a + t * z a)) = 1 ∧
      ∀ i, ∑ a, (p a + t * z a) * φ i a = k i := by
  constructor
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hp, hz]
  · intro i
    simp_rw [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmoment, hkernel]
    ring

theorem support_reduction_step {α ι : Type*} [Fintype α]
    (p z : α → ℝ) (φ : ι → α → ℝ) (k : ι → ℝ)
    (hp : ∀ a, 0 < p a) (hmass : ∑ a, p a = 1)
    (hz : z ≠ 0) (hsum : ∑ a, z a = 0)
    (hmoment : ∀ i, ∑ a, p a * φ i a = k i)
    (hkernel : ∀ i, ∑ a, z a * φ i a = 0)
    (horient : 0 ≤ lawOverlap p z) :
    ∃ t : ℝ, 0 < t ∧ (∀ a, 0 ≤ p a + t * z a) ∧
      (∃ a, p a + t * z a = 0) ∧
      (∑ a, (p a + t * z a)) = 1 ∧
      (∀ i, ∑ a, (p a + t * z a) * φ i a = k i) ∧
      collision p < collision (fun a => p a + t * z a) ∧
      MonotoneOn (fun u : ℝ => collision (fun a => p a + u * z a)) (Set.Ici 0) ∧
      0 ≤ lawOverlap p ((fun a => p a + t * z a) - p) := by
  have hnonzero : ∃ a ∈ (Finset.univ : Finset α), z a ≠ 0 := by
    by_contra! h
    apply hz
    funext a
    exact h a (Finset.mem_univ a)
  obtain ⟨a, _, ha⟩ :=
    Finset.exists_neg_of_sum_zero_of_exists_nonzero z hsum hnonzero
  obtain ⟨t, ht, hpositive, hkill⟩ := support_deletion_endpoint p z hp ⟨a, ha⟩
  obtain ⟨hm, hc⟩ := kernel_direction_feasible p z φ k hmass hsum hmoment hkernel t
  refine ⟨t, ht, hpositive, hkill, hm, hc,
    collision_direction_strict_increase p z hz horient t ht,
    collision_direction_monotone p z horient, ?_⟩
  have heq : lawOverlap p ((fun a => p a + t * z a) - p) = t * lawOverlap p z := by
    simp [lawOverlap, mul_add, mul_sub, ← Finset.mul_sum, mul_comm, mul_left_comm]
  rw [heq]
  exact mul_nonneg ht.le horient

end EntropyDesigns
