module

public import EntropyDesigns.ReductionEndpoint

/-! # Finite support reduction over an arbitrary ordered field

This includes the rational case, without an assumption that a real kernel
direction has rational coordinates. The proof constructs directions in the
same field as the input matrix and laws.
-/

@[expose] public section
namespace EntropyDesigns.FieldReduction
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def collision {α : Type*} [Fintype α] (p : α → K) : K := ∑ a, p a ^ 2

def lawOverlap {α : Type*} [Fintype α] (p z : α → K) : K := ∑ a, p a * z a

theorem collision_pos_of_ne_zero {α : Type*} [Fintype α]
    (z : α → K) (hz : z ≠ 0) : 0 < collision z := by
  classical
  have hnonzero : ∃ a, z a ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  obtain ⟨a, ha⟩ := hnonzero
  exact Finset.sum_pos' (fun i _ => sq_nonneg (z i))
    ⟨a, Finset.mem_univ a, sq_pos_of_ne_zero ha⟩

/- Source development: SupportReduction.lean. -/
theorem lawOverlap_sub {α : Type*} [Fintype α] (p q r : α → K) :
    lawOverlap p (q - r) = lawOverlap p q - lawOverlap p r := by
  simp [lawOverlap, mul_sub, Finset.sum_sub_distrib]

theorem lawOverlap_self {α : Type*} [Fintype α] (p : α → K) :
    lawOverlap p p = collision p := by
  simp [lawOverlap, collision, pow_two]

theorem support_deletion_endpoint {α : Type*} [Fintype α]
    (p z : α → K) (hp : ∀ a, 0 < p a)
    (hneg : ∃ a, z a < 0) :
    ∃ t : K, 0 < t ∧ (∀ a, 0 ≤ p a + t * z a) ∧
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
    (p z : α → K) (t : K) :
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
    (p z : α → K) (hz : z ≠ 0) (horient : 0 ≤ lawOverlap p z)
    (t : K) (ht : 0 < t) :
    collision p < collision (fun a => p a + t * z a) := by
  have hpos := collision_pos_of_ne_zero z hz
  rw [collision_direction_expansion]
  have hlin : 0 ≤ 2 * t * lawOverlap p z :=
    mul_nonneg (by positivity) horient
  have hquad : 0 < t ^ 2 * collision z := mul_pos (sq_pos_of_pos ht) hpos
  linarith

theorem collision_direction_monotone {α : Type*} [Fintype α]
    (p z : α → K) (horient : 0 ≤ lawOverlap p z) :
    MonotoneOn (fun t : K => collision (fun a => p a + t * z a))
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
    (p z : α → K) (φ : ι → α → K) (k : ι → K)
    (hp : ∑ a, p a = 1) (hz : ∑ a, z a = 0)
    (hmoment : ∀ i, ∑ a, p a * φ i a = k i)
    (hkernel : ∀ i, ∑ a, z a * φ i a = 0) (t : K) :
    (∑ a, (p a + t * z a)) = 1 ∧
      ∀ i, ∑ a, (p a + t * z a) * φ i a = k i := by
  constructor
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hp, hz]
  · intro i
    simp_rw [add_mul, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmoment, hkernel]
    ring

theorem support_reduction_step {α ι : Type*} [Fintype α]
    (p z : α → K) (φ : ι → α → K) (k : ι → K)
    (hp : ∀ a, 0 < p a) (hmass : ∑ a, p a = 1)
    (hz : z ≠ 0) (hsum : ∑ a, z a = 0)
    (hmoment : ∀ i, ∑ a, p a * φ i a = k i)
    (hkernel : ∀ i, ∑ a, z a * φ i a = 0)
    (horient : 0 ≤ lawOverlap p z) :
    ∃ t : K, 0 < t ∧ (∀ a, 0 ≤ p a + t * z a) ∧
      (∃ a, p a + t * z a = 0) ∧
      (∑ a, (p a + t * z a)) = 1 ∧
      (∀ i, ∑ a, (p a + t * z a) * φ i a = k i) ∧
      collision p < collision (fun a => p a + t * z a) ∧
      MonotoneOn (fun u : K => collision (fun a => p a + u * z a)) (Set.Ici 0) ∧
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

/- Source development: SupportKernel.lean. -/
theorem dependent_columns_kernel {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α K) (hdep : ¬ LinearIndependent K A.col) :
    ∃ z : α → K, z ≠ 0 ∧ A.mulVec z = 0 := by
  classical
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨z, hlinear, a, ha⟩ := hdep
  refine ⟨z, ?_, ?_⟩
  · intro h
    exact ha (congrFun h a)
  · funext r
    have h := congrFun hlinear r
    simpa [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm] using h

theorem oriented_kernel_direction {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α K) (p : α → K)
    (hdep : ¬ LinearIndependent K A.col) :
    ∃ z : α → K, z ≠ 0 ∧ A.mulVec z = 0 ∧ 0 ≤ lawOverlap p z := by
  obtain ⟨z, hz, hkernel⟩ := dependent_columns_kernel A hdep
  by_cases h : 0 ≤ lawOverlap p z
  · exact ⟨z, hz, hkernel, h⟩
  · refine ⟨-z, ?_, ?_, ?_⟩
    · simpa using hz
    · simpa [Matrix.mulVec_neg] using congrArg Neg.neg hkernel
    · have hneg : lawOverlap p (-z) = -lawOverlap p z := by
        simp [lawOverlap, Finset.sum_neg_distrib]
      rw [hneg]
      linarith

theorem dependent_support_deletion {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K)
    (hp : ∀ a, 0 < p a) (hmass : ∑ a, p a = 1) (hfeasible : A.mulVec p = b)
    (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1)
    (hdep : ¬ LinearIndependent K A.col) :
    ∃ q : α → K, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
      collision p < collision q ∧ (Finset.univ.filter (fun a => q a ≠ 0)).card < Fintype.card α ∧
      0 ≤ lawOverlap p (q - p) := by
  classical
  obtain ⟨z, hz, hkernel, horient⟩ := oriented_kernel_direction A p hdep
  have hsum : ∑ a, z a = 0 := by
    have h := congrFun hkernel i₀
    simpa [Matrix.mulVec, dotProduct, hconstant] using h
  have hmoment : ∀ i, ∑ a, p a * A i a = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hfeasible i
  have hzero : ∀ i, ∑ a, z a * A i a = 0 := by
    intro i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hkernel i
  obtain ⟨t, ht, hq, hkill, hmassq, hmomentq, hcollision, _, horientation⟩ :=
    support_reduction_step p z (fun i a => A i a) b hp hmass hz hsum hmoment hzero horient
  let q := fun a => p a + t * z a
  refine ⟨q, hq, hmassq, ?_, hcollision, ?_, horientation⟩
  · funext i
    simpa [q, Matrix.mulVec, dotProduct, mul_comm] using hmomentq i
  · obtain ⟨a, ha⟩ := hkill
    have hproper : Finset.univ.filter (fun a => q a ≠ 0) ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      intro heq
      have ha' : a ∈ Finset.univ.filter (fun a => q a ≠ 0) := by rw [heq]; exact Finset.mem_univ a
      exact (Finset.mem_filter.mp ha').2 ha
    simpa using Finset.card_lt_card hproper

/- Source development: SupportRestriction.lean. -/
noncomputable def activeSupport {α : Type*} [Fintype α] (p : α → K) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => p a ≠ 0)

def extendWeights {α : Type*} [DecidableEq α] (S : Finset α) (w : S → K) (a : α) : K :=
  if h : a ∈ S then w ⟨a, h⟩ else 0

theorem extendWeights_on {α : Type*} [DecidableEq α] (S : Finset α)
    (w : S → K) (a : S) : extendWeights S w a = w a := by
  simp [extendWeights, a.property]

theorem extendWeights_sum {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → K) (f : K → K) (hf : f 0 = 0) :
    (∑ a, f (extendWeights S w a)) = ∑ a : S, f (w a) := by
  have heq := Finset.sum_subtype (F := inferInstance) S (fun _ => Iff.rfl) (fun a => f (extendWeights S w a))
  simp only [extendWeights_on] at heq
  rw [← heq]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro a _ ha
  simp [extendWeights, ha, hf]

theorem extendWeights_moment {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → K) (g : α → K) :
    (∑ a, extendWeights S w a * g a) = ∑ a : S, w a * g a := by
  have heq := Finset.sum_subtype (F := inferInstance) S (fun _ => Iff.rfl) (fun a => extendWeights S w a * g a)
  simp only [extendWeights_on] at heq
  rw [← heq]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro a _ ha
  simp [extendWeights, ha]

theorem activeSupport_sum {α : Type*} [Fintype α] (p : α → K) (g : α → K) :
    (∑ a : activeSupport p, p a * g a) = ∑ a, p a * g a := by
  classical
  rw [← Finset.sum_subtype (activeSupport p) (fun _ => Iff.rfl) (fun a => p a * g a)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hp : p a = 0 := by simpa [activeSupport] using ha
  simp [hp]

theorem extendWeights_nonneg {α : Type*} [DecidableEq α] (S : Finset α)
    (w : S → K) (hw : ∀ a, 0 ≤ w a) : ∀ a, 0 ≤ extendWeights S w a := by
  intro a
  unfold extendWeights
  split_ifs with h
  · exact hw ⟨a, h⟩
  · exact le_rfl

theorem extendWeights_support_subset {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → K) : activeSupport (extendWeights S w) ⊆ S := by
  classical
  intro a ha
  by_contra h
  have hnonzero := (Finset.mem_filter.mp ha).2
  exact hnonzero (by simp [extendWeights, h])

theorem extendWeights_support_card {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → K) :
    (activeSupport (extendWeights S w)).card = (activeSupport w).card := by
  classical
  have heq : activeSupport (extendWeights S w) =
      (activeSupport w).image (fun a : S => (a : α)) := by
    ext a
    constructor
    · intro ha
      have hmem := extendWeights_support_subset S w ha
      refine Finset.mem_image.mpr ⟨⟨a, hmem⟩, ?_, rfl⟩
      have hnonzero := (Finset.mem_filter.mp ha).2
      simpa [activeSupport, extendWeights, hmem] using hnonzero
    · intro ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      have hnonzero := (Finset.mem_filter.mp hb).2
      simpa [activeSupport, extendWeights_on] using hnonzero
  rw [heq, Finset.card_image_of_injective _ Subtype.val_injective]

/- Source development: SupportDescent.lean. -/
theorem active_support_deletion {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (hfeasible : A.mulVec p = b)
    (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1)
    (hdep : ¬ LinearIndependent K (A.submatrix id (fun a : activeSupport p => (a : α))).col) :
    ∃ q : α → K, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
      collision p < collision q ∧ activeSupport q ⊆ activeSupport p ∧
      (activeSupport q).card < (activeSupport p).card ∧ 0 ≤ lawOverlap p (q - p) := by
  classical
  let S := activeSupport p
  let pS : S → K := fun a => p a
  let AS := A.submatrix id (fun a : S => (a : α))
  have hpositive : ∀ a, 0 < pS a := by
    intro a
    exact lt_of_le_of_ne (hp a) (Ne.symm (Finset.mem_filter.mp a.property).2)
  have hmassS : ∑ a, pS a = 1 := by
    have h := activeSupport_sum p (fun _ => 1)
    simp only [mul_one] at h
    exact h.trans hmass
  have hfeasibleS : AS.mulVec pS = b := by
    funext i
    have hsum := activeSupport_sum p (fun a => A i a)
    have hi := congrFun hfeasible i
    simpa [AS, pS, S, Matrix.mulVec, dotProduct, mul_comm] using hsum.trans
      (by simpa [Matrix.mulVec, dotProduct, mul_comm] using hi)
  obtain ⟨w, hw, hmassw, hAw, hcollisionw, hcardw, horientationw⟩ :=
    dependent_support_deletion AS b pS hpositive hmassS hfeasibleS i₀
      (fun a => hconstant a) hdep
  let q := extendWeights S w
  have hcollisionp : collision pS = collision p := by
    simpa [collision, pS, S, pow_two] using activeSupport_sum p p
  have hcollisionq : collision q = collision w :=
    extendWeights_sum S w (fun x => x ^ 2) (by norm_num)
  refine ⟨q, extendWeights_nonneg S w hw, ?_, ?_, ?_,
    extendWeights_support_subset S w, ?_, ?_⟩
  · exact (extendWeights_sum S w id rfl).trans hmassw
  · funext i
    have hsum := extendWeights_moment S w (fun a => A i a)
    have hi := congrFun hAw i
    simpa [q, Matrix.mulVec, dotProduct, AS, mul_comm] using hsum.trans
      (by simpa [Matrix.mulVec, dotProduct, AS, mul_comm] using hi)
  · rw [hcollisionq, ← hcollisionp]
    exact hcollisionw
  · rw [extendWeights_support_card S w]
    change (activeSupport w).card < S.card
    simpa only [activeSupport, Fintype.card_coe] using hcardw
  · have hcross : lawOverlap p q = lawOverlap pS w := by
      simpa [lawOverlap, mul_comm] using extendWeights_moment S w p
    rwa [lawOverlap_sub, lawOverlap_self, hcross, ← hcollisionp,
      ← lawOverlap_self, ← lawOverlap_sub]

theorem independent_support_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (hfeasible : A.mulVec p = b)
    (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ q : α → K, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
      collision p ≤ collision q ∧ activeSupport q ⊆ activeSupport p ∧
      LinearIndependent K (A.submatrix id (fun a : activeSupport q => (a : α))).col := by
  classical
  have h : ∀ m : ℕ, ∀ p : α → K, (activeSupport p).card = m →
      (∀ a, 0 ≤ p a) → (∑ a, p a = 1) → A.mulVec p = b →
      ∃ q : α → K, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
        collision p ≤ collision q ∧ activeSupport q ⊆ activeSupport p ∧
        LinearIndependent K (A.submatrix id (fun a : activeSupport q => (a : α))).col := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hcard hp hmass hfeasible
      by_cases hlin : LinearIndependent K
          (A.submatrix id (fun a : activeSupport p => (a : α))).col
      · exact ⟨p, hp, hmass, hfeasible, le_rfl, Finset.Subset.refl _, hlin⟩
      · obtain ⟨q, hq, hmq, hAq, hCq, hsubq, hcardq, _⟩ :=
          active_support_deletion A b p hp hmass hfeasible i₀ hconstant hlin
        obtain ⟨w, hw, hmw, hAw, hCw, hsubw, hlinw⟩ :=
          ih (activeSupport q).card (by omega) q rfl hq hmq hAq
        exact ⟨w, hw, hmw, hAw, hCq.le.trans hCw, hsubw.trans hsubq, hlinw⟩
  exact h (activeSupport p).card p rfl hp hmass hfeasible

theorem independent_support_card_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α K) (q : α → K)
    (hlin : LinearIndependent K (A.submatrix id (fun a : activeSupport q => (a : α))).col) :
    (activeSupport q).card ≤ Fintype.card ι := by
  simpa only [Fintype.card_coe, Module.finrank_pi, Module.finrank_self, mul_one] using
    hlin.fintype_card_le_finrank

/- Source development: SupportDimension.lean. -/
def supportedKernel {ι α : Type*} [Fintype α] (A : Matrix ι α K)
    (S : Finset α) : Submodule K (α → K) where
  carrier := {z | A.mulVec z = 0 ∧ ∀ a, a ∉ S → z a = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    intro z w hz hw
    exact ⟨by simp [Matrix.mulVec_add, hz.1, hw.1],
      fun a ha => by simp [hz.2 a ha, hw.2 a ha]⟩
  smul_mem' := by
    intro c z hz
    exact ⟨by simp [Matrix.mulVec_smul, hz.1], fun a ha => by simp [hz.2 a ha]⟩

theorem matrix_extendWeights {ι α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix ι α K) (S : Finset α) (w : S → K) :
    A.mulVec (extendWeights S w) = (A.submatrix id (fun a : S => (a : α))).mulVec w := by
  funext i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using
    extendWeights_moment S w (fun a => A i a)

theorem extendWeights_restrict {α : Type*} [DecidableEq α]
    (S : Finset α) (z : α → K) (hz : ∀ a, a ∉ S → z a = 0) :
    extendWeights S (fun a => z a) = z := by
  funext a
  by_cases ha : a ∈ S <;> simp [extendWeights, ha, hz a]

theorem supportedKernel_dimension {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (S : Finset α) :
    Module.finrank K (supportedKernel A S) =
      S.card - (A.submatrix id (fun a : S => (a : α))).rank := by
  classical
  let AS := A.submatrix id (fun a : S => (a : α))
  let Ker := LinearMap.ker AS.mulVecLin
  let E : Ker →ₗ[K] supportedKernel A S := {
    toFun := fun w => ⟨extendWeights S w, by
      constructor
      · rw [matrix_extendWeights]
        exact w.property
      · intro a ha
        simp [extendWeights, ha]⟩
    map_add' := by
      intro w v
      apply Subtype.ext
      funext a
      by_cases ha : a ∈ S <;> simp [extendWeights, ha]
    map_smul' := by
      intro c w
      apply Subtype.ext
      funext a
      by_cases ha : a ∈ S <;> simp [extendWeights, ha] }
  have hinj : Function.Injective E := by
    intro w v h
    apply Subtype.ext
    funext a
    have hi := congrArg (fun z : supportedKernel A S => z.val a) h
    simpa [E, extendWeights_on] using hi
  have hsurj : Function.Surjective E := by
    intro z
    have hext : extendWeights S (fun a => z.val a) = z.val :=
      extendWeights_restrict S z.val z.property.2
    have hker : (fun a : S => z.val a) ∈ Ker := by
      change AS.mulVec (fun a => z.val a) = 0
      rw [← matrix_extendWeights, hext]
      exact z.property.1
    refine ⟨⟨fun a => z.val a, hker⟩, ?_⟩
    apply Subtype.ext
    exact hext
  have hdim := (LinearEquiv.ofBijective E ⟨hinj, hsurj⟩).finrank_eq
  have hrank := AS.mulVecLin.finrank_range_add_finrank_ker
  have hsum : AS.rank + Module.finrank K Ker = S.card := by
    simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self,
      mul_one, Fintype.card_coe] using hrank
  change Module.finrank K (supportedKernel A S) = S.card - AS.rank
  omega

theorem supportedKernel_mono {ι α : Type*} [Fintype α]
    (A : Matrix ι α K) (S T : Finset α) (hST : S ⊆ T) :
    supportedKernel A S ≤ supportedKernel A T := by
  intro z hz
  exact ⟨hz.1, fun a ha => hz.2 a (fun h => ha (hST h))⟩

theorem support_dimension_strict_drop {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (p q : α → K)
    (hfeasible : A.mulVec p = A.mulVec q)
    (hsub : activeSupport q ⊆ activeSupport p)
    (hcard : (activeSupport q).card < (activeSupport p).card) :
    (activeSupport q).card -
        (A.submatrix id (fun a : activeSupport q => (a : α))).rank <
      (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank := by
  classical
  have hreverse : ¬ activeSupport p ⊆ activeSupport q := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨a, hap, haq⟩ := Finset.not_subset.mp hreverse
  have hpa : p a ≠ 0 := (Finset.mem_filter.mp hap).2
  have hqa : q a = 0 := by simpa [activeSupport] using haq
  have hv : p - q ∈ supportedKernel A (activeSupport p) := by
    constructor
    · rw [Matrix.mulVec_sub, hfeasible, sub_self]
    · intro x hx
      have hpx : p x = 0 := by simpa [activeSupport] using hx
      have hqx : q x = 0 := by
        have hnot : x ∉ activeSupport q := fun h => hx (hsub h)
        simpa [activeSupport] using hnot
      simp [hpx, hqx]
  have hnot : p - q ∉ supportedKernel A (activeSupport q) := by
    intro h
    have hzero := h.2 a haq
    have : p a = 0 := by simpa [hqa] using hzero
    exact hpa this
  have hlt : supportedKernel A (activeSupport q) < supportedKernel A (activeSupport p) := by
    refine lt_of_le_of_ne (supportedKernel_mono A _ _ hsub) ?_
    intro heq
    exact hnot (heq.symm ▸ hv)
  rw [← supportedKernel_dimension, ← supportedKernel_dimension]
  exact Submodule.finrank_lt_finrank_of_lt hlt

/- Source development: BoundedReduction.lean. -/
def feasibleLaw {ι α : Type*} [Fintype α] (A : Matrix ι α K)
    (b : ι → K) (p : α → K) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧ A.mulVec p = b

def reductionStep {ι α : Type*} [Fintype α] (A : Matrix ι α K)
    (b : ι → K) (p q : α → K) : Prop :=
  feasibleLaw A b q ∧ collision p < collision q ∧
    activeSupport q ⊆ activeSupport p ∧ (activeSupport q).card < (activeSupport p).card ∧
    0 ≤ lawOverlap p (q - p)

theorem bounded_support_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K)
    (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ k : ℕ, k ≤ (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧
      ∃ path : Fin (k + 1) → (α → K),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        feasibleLaw A b (path (Fin.last k)) ∧
        LinearIndependent K
          (A.submatrix id (fun a : activeSupport (path (Fin.last k)) => (a : α))).col := by
  classical
  let D := fun p : α → K => (activeSupport p).card -
    (A.submatrix id (fun a : activeSupport p => (a : α))).rank
  have h : ∀ m : ℕ, ∀ p : α → K, D p = m → feasibleLaw A b p →
      ∃ k : ℕ, k ≤ D p ∧ ∃ path : Fin (k + 1) → (α → K),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        feasibleLaw A b (path (Fin.last k)) ∧
        LinearIndependent K
          (A.submatrix id (fun a : activeSupport (path (Fin.last k)) => (a : α))).col := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hD hp
      by_cases hlin : LinearIndependent K
          (A.submatrix id (fun a : activeSupport p => (a : α))).col
      · refine ⟨0, Nat.zero_le _, fun _ => p, rfl, ?_, hp, hlin⟩
        intro j
        exact Fin.elim0 j
      · obtain ⟨q, hq, hmq, hAq, hCq, hsubq, hcardq, horientationq⟩ :=
          active_support_deletion A b p hp.1 hp.2.1 hp.2.2 i₀ hconstant hlin
        have hdim : D q < D p := support_dimension_strict_drop A p q
          (hp.2.2.trans hAq.symm) hsubq hcardq
        have hfeasibleq : feasibleLaw A b q := ⟨hq, hmq, hAq⟩
        obtain ⟨k, hk, path, hfirst, hsteps, hlast, hlinlast⟩ :=
          ih (D q) (by omega) q rfl hfeasibleq
        let path' : Fin (k + 1 + 1) → (α → K) := Fin.cases p path
        have hlast' : path' (Fin.last (k + 1)) = path (Fin.last k) := rfl
        refine ⟨k + 1, by omega, path', rfl, ?_, ?_, ?_⟩
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · have hstep : reductionStep A b p q :=
              ⟨hfeasibleq, hCq, hsubq, hcardq, horientationq⟩
            change reductionStep A b p (path ⟨0, Nat.zero_lt_succ k⟩)
            rw [hfirst]
            exact hstep
          · exact hsteps j
        · rwa [hlast']
        · rwa [hlast']
  exact h (D p) p rfl hp

/- Source development: SupportVertex.lean. -/
theorem independent_support_unique {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (p q : α → K)
    (hlin : LinearIndependent K (A.submatrix id (fun a : activeSupport p => (a : α))).col)
    (hsupport : ∀ a, a ∉ activeSupport p → q a = 0)
    (hfeasible : A.mulVec q = A.mulVec p) : q = p := by
  classical
  let S := activeSupport p
  have hp : extendWeights S (fun a => p a) = p := extendWeights_restrict S p (by
    intro a ha
    simpa [S, activeSupport] using ha)
  have hq : extendWeights S (fun a => q a) = q := extendWeights_restrict S q hsupport
  have hrestricted : (A.submatrix id (fun a : S => (a : α))).mulVec (fun a => q a) =
      (A.submatrix id (fun a : S => (a : α))).mulVec (fun a => p a) := by
    rw [← matrix_extendWeights, ← matrix_extendWeights, hq, hp]
    exact hfeasible
  have hvalues := (Matrix.mulVec_injective_iff.mpr hlin) hrestricted
  exact hq.symm.trans ((congrArg (extendWeights S) hvalues).trans hp)

theorem independent_support_vertex {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K)
    (hp : feasibleLaw A b p)
    (hlin : LinearIndependent K (A.submatrix id (fun a : activeSupport p => (a : α))).col) :
    p ∈ Set.extremePoints K {q | feasibleLaw A b q} := by
  classical
  refine ⟨hp, ?_⟩
  intro x hx y hy hsegment
  obtain ⟨a, c, ha, hc, hac, hcombo⟩ := hsegment
  apply independent_support_unique A p x hlin ?_ (hx.2.2.trans hp.2.2.symm)
  intro j hj
  have hpj : p j = 0 := by simpa [activeSupport] using hj
  have h := congrFun hcombo j
  change a * x j + c * y j = p j at h
  have hnonneg : 0 ≤ c * y j := mul_nonneg hc.le (hy.1 j)
  have hxj := hx.1 j
  have hxzero : a * x j = 0 := by nlinarith
  exact (mul_eq_zero.mp hxzero).resolve_left ha.ne'

/- Source development: ReductionEndpoint.lean. -/
theorem reductionStep_exact_endpoint {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α K) (b : ι → K) (p q : α → K)
    (hp : feasibleLaw A b p) (hstep : reductionStep A b p q) :
    ∃ z : α → K, z ≠ 0 ∧ A.mulVec z = 0 ∧ 0 ≤ lawOverlap p z ∧
      q = (fun a => p a + z a) ∧
      (∀ a, z a < 0 → 1 ≤ p a / (-z a)) ∧
      (∃ a, z a < 0 ∧ p a / (-z a) = 1) := by
  classical
  refine ⟨q - p, ?_, ?_, hstep.2.2.2.2, ?_, ?_, ?_⟩
  · intro hz
    have hqp : q = p := sub_eq_zero.mp hz
    have h := hstep.2.1
    simpa [hqp] using h
  · rw [Matrix.mulVec_sub, hstep.1.2.2, hp.2.2, sub_self]
  · funext a
    simp
  · intro a ha
    apply (le_div_iff₀ (neg_pos.mpr ha)).2
    dsimp only [Pi.sub_apply]
    linarith [hstep.1.1 a]
  · have hreverse : ¬ activeSupport p ⊆ activeSupport q := by
      intro h
      have := Finset.card_le_card h
      have := hstep.2.2.2.1
      omega
    obtain ⟨a, hap, haq⟩ := Finset.not_subset.mp hreverse
    have hpa : 0 < p a := lt_of_le_of_ne (hp.1 a)
      (Ne.symm (Finset.mem_filter.mp hap).2)
    have hqa : q a = 0 := by simpa [activeSupport] using haq
    refine ⟨a, ?_, ?_⟩
    · simpa [hqa] using neg_neg_of_pos hpa
    · simp [hqa, hpa.ne']

theorem reductionStep_interpolation {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α K) (b : ι → K) (p q : α → K)
    (hp : feasibleLaw A b p) (hstep : reductionStep A b p q) :
    (∀ u : K, 0 ≤ u → u ≤ 1 →
      feasibleLaw A b (fun a => p a + u * (q - p) a)) ∧
    MonotoneOn (fun u : K => collision (fun a => p a + u * (q - p) a)) (Set.Ici 0) := by
  refine ⟨?_, collision_direction_monotone p (q - p) hstep.2.2.2.2⟩
  intro u hu hu'
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have h1 := mul_nonneg (by linarith : 0 ≤ 1 - u) (hp.1 a)
    have h2 := mul_nonneg hu (hstep.1.1 a)
    dsimp only [Pi.sub_apply]
    nlinarith
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hp.2.1, hstep.1.2.1]
  · change A.mulVec (p + u • (q - p)) = b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
      hp.2.2, hstep.1.2.2, sub_self, smul_zero, add_zero]

theorem bounded_vertex_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K)
    (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ k : ℕ, k ≤ (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧
      ∃ path : Fin (k + 1) → (α → K),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        path (Fin.last k) ∈ Set.extremePoints K {q | feasibleLaw A b q} ∧
        (activeSupport (path (Fin.last k))).card ≤ Fintype.card ι := by
  obtain ⟨k, hk, path, hfirst, hsteps, hlast, hlin⟩ :=
    bounded_support_reduction A b p hp i₀ hconstant
  exact ⟨k, hk, path, hfirst, hsteps, independent_support_vertex A b _ hlast hlin,
    independent_support_card_bound A _ hlin⟩

theorem rational_bounded_vertex_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℚ) (b : ι → ℚ) (p : α → ℚ)
    (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ k : ℕ, k ≤ (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧
      ∃ path : Fin (k + 1) → (α → ℚ),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        path (Fin.last k) ∈ Set.extremePoints ℚ {q | feasibleLaw A b q} ∧
        (activeSupport (path (Fin.last k))).card ≤ Fintype.card ι :=
  bounded_vertex_reduction A b p hp i₀ hconstant

end EntropyDesigns.FieldReduction
