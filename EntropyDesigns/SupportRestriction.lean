module

public import EntropyDesigns.SupportKernel

/-! # Restriction and extension of finite laws on their actual support -/

@[expose] public section
namespace EntropyDesigns

noncomputable def activeSupport {α : Type*} [Fintype α] (p : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => p a ≠ 0)

def extendWeights {α : Type*} [DecidableEq α] (S : Finset α) (w : S → ℝ) (a : α) : ℝ :=
  if h : a ∈ S then w ⟨a, h⟩ else 0

theorem extendWeights_on {α : Type*} [DecidableEq α] (S : Finset α)
    (w : S → ℝ) (a : S) : extendWeights S w a = w a := by
  simp [extendWeights, a.property]

theorem extendWeights_sum {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → ℝ) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ a, f (extendWeights S w a)) = ∑ a : S, f (w a) := by
  have heq := Finset.sum_subtype (F := inferInstance) S (fun _ => Iff.rfl) (fun a => f (extendWeights S w a))
  simp only [extendWeights_on] at heq
  rw [← heq]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro a _ ha
  simp [extendWeights, ha, hf]

theorem extendWeights_moment {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → ℝ) (g : α → ℝ) :
    (∑ a, extendWeights S w a * g a) = ∑ a : S, w a * g a := by
  have heq := Finset.sum_subtype (F := inferInstance) S (fun _ => Iff.rfl) (fun a => extendWeights S w a * g a)
  simp only [extendWeights_on] at heq
  rw [← heq]
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro a _ ha
  simp [extendWeights, ha]

theorem activeSupport_sum {α : Type*} [Fintype α] (p : α → ℝ) (g : α → ℝ) :
    (∑ a : activeSupport p, p a * g a) = ∑ a, p a * g a := by
  classical
  rw [← Finset.sum_subtype (activeSupport p) (fun _ => Iff.rfl) (fun a => p a * g a)]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  have hp : p a = 0 := by simpa [activeSupport] using ha
  simp [hp]

theorem extendWeights_nonneg {α : Type*} [DecidableEq α] (S : Finset α)
    (w : S → ℝ) (hw : ∀ a, 0 ≤ w a) : ∀ a, 0 ≤ extendWeights S w a := by
  intro a
  unfold extendWeights
  split_ifs with h
  · exact hw ⟨a, h⟩
  · exact le_rfl

theorem extendWeights_support_subset {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → ℝ) : activeSupport (extendWeights S w) ⊆ S := by
  classical
  intro a ha
  by_contra h
  have hnonzero := (Finset.mem_filter.mp ha).2
  exact hnonzero (by simp [extendWeights, h])

theorem extendWeights_support_card {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (w : S → ℝ) :
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

end EntropyDesigns
