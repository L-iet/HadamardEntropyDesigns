module

public import EntropyDesigns.Entropy

/-! # Exact collision minima along straight probability bridges -/

@[expose] public section
namespace EntropyDesigns

def probabilityBlend {α : Type*} (p q : α → ℝ) (t : ℝ) (a : α) : ℝ :=
  (1 - t) * p a + t * q a

def lawOverlap {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * q a

noncomputable def bridgeTime (a b c : ℝ) : ℝ :=
  max (a - c) 0 / (a + b - 2 * c)

noncomputable def bridgeLoss (a b c : ℝ) : ℝ :=
  (max (a - c) 0) ^ 2 / (a + b - 2 * c)

theorem collision_blend_expansion {α : Type*} [Fintype α]
    (p q : α → ℝ) (t : ℝ) :
    collision (probabilityBlend p q t) =
      collision p + 2 * (lawOverlap p q - collision p) * t +
        (collision p + collision q - 2 * lawOverlap p q) * t ^ 2 := by
  have hpoint : ∀ a, probabilityBlend p q t a ^ 2 =
      (1 - t) ^ 2 * p a ^ 2 + t ^ 2 * q a ^ 2 +
        (2 * t * (1 - t)) * (p a * q a) := by
    intro a
    unfold probabilityBlend
    ring
  unfold collision
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  unfold lawOverlap
  ring

theorem collision_distance_identity {α : Type*} [Fintype α] (p q : α → ℝ) :
    (∑ a, (p a - q a) ^ 2) =
      collision p + collision q - 2 * lawOverlap p q := by
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hmid : (∑ a, 2 * p a * q a) = 2 * lawOverlap p q := by
    unfold lawOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hmid]
  unfold collision
  ring

theorem collision_distance_pos {α : Type*} [Fintype α]
    (p q : α → ℝ) (hne : p ≠ q) :
    0 < collision p + collision q - 2 * lawOverlap p q := by
  classical
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  rw [← collision_distance_identity]
  have hpos : 0 < (p a - q a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr ha)
  exact hpos.trans_le (Finset.single_le_sum (fun b _ => sq_nonneg (p b - q b))
    (Finset.mem_univ a))

theorem bridge_quadratic_minimum {a b c : ℝ}
    (hba : a ≤ b) (he : 0 < a + b - 2 * c) :
    0 ≤ bridgeTime a b c ∧ bridgeTime a b c ≤ 1 / 2 ∧
    a + 2 * (c - a) * bridgeTime a b c +
        (a + b - 2 * c) * bridgeTime a b c ^ 2 = a - bridgeLoss a b c ∧
    ∀ t : ℝ, 0 ≤ t →
      a - bridgeLoss a b c ≤ a + 2 * (c - a) * t + (a + b - 2 * c) * t ^ 2 := by
  by_cases hca : a ≤ c
  · have ht : bridgeTime a b c = 0 := by
      simp [bridgeTime, max_eq_right (sub_nonpos.mpr hca)]
    have hl : bridgeLoss a b c = 0 := by
      simp [bridgeLoss, max_eq_right (sub_nonpos.mpr hca)]
    rw [ht, hl]
    refine ⟨le_rfl, by norm_num, by ring, ?_⟩
    intro t ht
    have hlin : 0 ≤ (c - a) * t := mul_nonneg (sub_nonneg.mpr hca) ht
    have hquad : 0 ≤ (a + b - 2 * c) * t ^ 2 := mul_nonneg he.le (sq_nonneg t)
    nlinarith
  · have hac : c < a := lt_of_not_ge hca
    have hmax : max (a - c) 0 = a - c := max_eq_left (sub_nonneg.mpr hac.le)
    have ht : 0 ≤ bridgeTime a b c := by
      unfold bridgeTime
      rw [hmax]
      exact div_nonneg (by linarith) he.le
    have hhalf : bridgeTime a b c ≤ 1 / 2 := by
      unfold bridgeTime
      rw [hmax]
      apply (div_le_iff₀ he).2
      linarith
    have heq : a + 2 * (c - a) * bridgeTime a b c +
        (a + b - 2 * c) * bridgeTime a b c ^ 2 = a - bridgeLoss a b c := by
      unfold bridgeTime bridgeLoss
      rw [hmax]
      field_simp
      ring
    refine ⟨ht, hhalf, heq, ?_⟩
    intro t _
    have hid : a + 2 * (c - a) * t + (a + b - 2 * c) * t ^ 2 -
        (a - bridgeLoss a b c) =
        (a + b - 2 * c) * (t - (a - c) / (a + b - 2 * c)) ^ 2 := by
      unfold bridgeLoss
      rw [hmax]
      field_simp
      ring
    have hnonneg := mul_nonneg he.le (sq_nonneg (t - (a - c) / (a + b - 2 * c)))
    linarith

theorem bridge_loss_upper {a b c : ℝ}
    (ha : 0 < a) (hba : a ≤ b) (hc : 0 ≤ c) (he : 0 < a + b - 2 * c) :
    bridgeLoss a b c ≤ a ^ 2 / (a + b) ∧ a ^ 2 / (a + b) ≤ a / 2 := by
  have hab : 0 < a + b := by linarith
  constructor
  · by_cases hca : a ≤ c
    · have hl : bridgeLoss a b c = 0 := by
        simp [bridgeLoss, max_eq_right (sub_nonpos.mpr hca)]
      rw [hl]
      exact div_nonneg (sq_nonneg a) hab.le
    · have hca' : c ≤ a := (lt_of_not_ge hca).le
      unfold bridgeLoss
      rw [max_eq_left (sub_nonneg.mpr hca')]
      apply (div_le_div_iff₀ he hab).2
      have hb : 0 ≤ b := by linarith
      have hcb : c ≤ b := hca'.trans hba
      have h₁ := mul_le_mul_of_nonneg_left hcb ha.le
      have h₂ := mul_le_mul_of_nonneg_left hca' hb
      have hinner : 0 ≤ 2 * a * b - c * (a + b) := by nlinarith
      have hprod := mul_nonneg hc hinner
      nlinarith [hprod]
  · apply (div_le_iff₀ hab).2
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hba)]

theorem bridge_loss_disjoint_value {a b : ℝ} (ha : 0 ≤ a) :
    bridgeLoss a b 0 = a ^ 2 / (a + b) := by
  simp [bridgeLoss, max_eq_left ha]

theorem probabilityBlend_nonneg {α : Type*} (p q : α → ℝ) (t : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∀ a, 0 ≤ probabilityBlend p q t a := by
  intro a
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht') (hp a)) (mul_nonneg ht (hq a))

theorem probabilityBlend_mass {α : Type*} [Fintype α]
    (p q : α → ℝ) (t : ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    (∑ a, probabilityBlend p q t a) = 1 := by
  unfold probabilityBlend
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hq]
  ring

theorem probabilityBlend_moment {α : Type*} [Fintype α]
    (p q φ : α → ℝ) (t k : ℝ)
    (hp : ∑ a, p a * φ a = k) (hq : ∑ a, q a * φ a = k) :
    (∑ a, probabilityBlend p q t a * φ a) = k := by
  have hpoint : ∀ a, probabilityBlend p q t a * φ a =
      (1 - t) * (p a * φ a) + t * (q a * φ a) := by
    intro a
    unfold probabilityBlend
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp, hq]
  ring

theorem bridge_quadratic_monotone {a b c : ℝ}
    (hca : a ≤ c) (he : 0 ≤ a + b - 2 * c) :
    MonotoneOn (fun t : ℝ => a + 2 * (c - a) * t + (a + b - 2 * c) * t ^ 2)
      (Set.Ici 0) := by
  intro s hs t ht hst
  change 0 ≤ s at hs
  change 0 ≤ t at ht
  have hlin := mul_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hst)
  have hsquare : s ^ 2 ≤ t ^ 2 := by nlinarith
  have hquad := mul_nonneg he (sub_nonneg.mpr hsquare)
  nlinarith

theorem straight_bridge_minimum {α : Type*} [Fintype α]
    (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hmass : ∑ a, p a = 1) (hne : p ≠ q) (hbetter : collision p ≤ collision q) :
    0 ≤ bridgeTime (collision p) (collision q) (lawOverlap p q) ∧
    bridgeTime (collision p) (collision q) (lawOverlap p q) ≤ 1 / 2 ∧
    collision (probabilityBlend p q (bridgeTime (collision p) (collision q) (lawOverlap p q))) =
      collision p - bridgeLoss (collision p) (collision q) (lawOverlap p q) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      collision (probabilityBlend p q (bridgeTime (collision p) (collision q) (lawOverlap p q))) ≤
        collision (probabilityBlend p q t)) ∧
    bridgeLoss (collision p) (collision q) (lawOverlap p q) ≤
      collision p ^ 2 / (collision p + collision q) ∧
    collision p ^ 2 / (collision p + collision q) ≤ collision p / 2 := by
  have ha := collision_pos p hp hmass
  have hc : 0 ≤ lawOverlap p q :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (hq a))
  have he := collision_distance_pos p q hne
  have hmin := bridge_quadratic_minimum hbetter he
  have hbound := bridge_loss_upper ha hbetter hc he
  refine ⟨hmin.1, hmin.2.1, ?_, ?_, hbound.1, hbound.2⟩
  · rw [collision_blend_expansion]
    exact hmin.2.2.1
  · intro t ht _
    rw [collision_blend_expansion, collision_blend_expansion, hmin.2.2.1]
    exact hmin.2.2.2 t ht

theorem straight_bridge_monotone {α : Type*} [Fintype α]
    (p q : α → ℝ) (hne : p ≠ q) (hca : collision p ≤ lawOverlap p q) :
    MonotoneOn (fun t : ℝ => collision (probabilityBlend p q t)) (Set.Ici 0) := by
  have hmono := bridge_quadratic_monotone hca (collision_distance_pos p q hne).le
  simpa only [collision_blend_expansion] using hmono

theorem lawOverlap_zero_of_disjoint {α : Type*} [Fintype α]
    (p q : α → ℝ) (hdisjoint : ∀ a, p a = 0 ∨ q a = 0) :
    lawOverlap p q = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  rcases hdisjoint a with h | h <;> simp [h]

theorem disjoint_bridge_loss_sharp {α : Type*} [Fintype α]
    (p q : α → ℝ) (_hp : ∀ a, 0 ≤ p a)
    (hdisjoint : ∀ a, p a = 0 ∨ q a = 0) :
    bridgeLoss (collision p) (collision q) (lawOverlap p q) =
      collision p ^ 2 / (collision p + collision q) := by
  rw [lawOverlap_zero_of_disjoint p q hdisjoint]
  exact bridge_loss_disjoint_value (Finset.sum_nonneg (fun a _ => sq_nonneg (p a)))

/-- All probability and prescribed linear-moment constraints are retained
along the entire unit-interval bridge. -/
theorem probabilityBlend_feasible {α ι : Type*} [Fintype α]
    (p q : α → ℝ) (φ : ι → α → ℝ) (k : ι → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hmassp : ∑ a, p a = 1) (hmassq : ∑ a, q a = 1)
    (hmomentp : ∀ i, ∑ a, p a * φ i a = k i)
    (hmomentq : ∀ i, ∑ a, q a * φ i a = k i)
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    (∀ a, 0 ≤ probabilityBlend p q t a) ∧
    (∑ a, probabilityBlend p q t a = 1) ∧
    (∀ i, ∑ a, probabilityBlend p q t a * φ i a = k i) :=
  ⟨probabilityBlend_nonneg p q t hp hq ht ht',
    probabilityBlend_mass p q t hmassp hmassq,
    fun i => probabilityBlend_moment p q (φ i) t (k i) (hmomentp i) (hmomentq i)⟩

end EntropyDesigns
