/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
At most two generators for weight-eight binary check spaces on twelve labels. -/
module
public import EntropyQuadraticClassification.ConstantWeightChecks
public import Mathlib.LinearAlgebra.Span.Basic
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem binary_singleton_span
    (D : Submodule (ZMod 2) (ι → ZMod 2)) {h : ι → ZMod 2}
    (hh : h∈D) (hall : ∀ f∈D,f=0 ∨ f=h) :
    D=Submodule.span (ZMod 2) {h} := by
  apply le_antisymm
  · intro f hf
    rcases hall f hf with rfl|rfl
    · exact Submodule.zero_mem _
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro f hf
    have he : f=h := by simpa using hf
    subst f
    exact hh

theorem binary_pair_span
    (D : Submodule (ZMod 2) (ι → ZMod 2)) {h g : ι → ZMod 2}
    (hh : h∈D) (hg : g∈D) (hall : ∀ f∈D,f=0 ∨ f=h ∨ f=g ∨ f=h+g) :
    D=Submodule.span (ZMod 2) {h,g} := by
  have hh' : h∈Submodule.span (ZMod 2) {h,g} :=
    Submodule.subset_span (by simp)
  have hg' : g∈Submodule.span (ZMod 2) {h,g} :=
    Submodule.subset_span (by simp)
  apply le_antisymm
  · intro f hf
    rcases hall f hf with rfl|rfl|rfl|rfl
    · exact Submodule.zero_mem _
    · exact hh'
    · exact hg'
    · exact Submodule.add_mem _ hh' hg'
  · apply Submodule.span_le.mpr
    intro f hf
    have he : f=h ∨ f=g := by simpa using hf
    rcases he with rfl|rfl
    · exact hh
    · exact hg

theorem constant_weight_generators (hι : Fintype.card ι=12)
    (D : Submodule (ZMod 2) (ι → ZMod 2))
    (hw : ∀ f∈D,f≠0 → (oneSupport f).card=8) :
    D=⊥ ∨ ∃ h∈D,h≠0 ∧
      (D=Submodule.span (ZMod 2) {h} ∨
        ∃ g∈D,g≠0 ∧ h≠g ∧ D=Submodule.span (ZMod 2) {h,g}) := by
  classical
  by_cases hall : ∀ f∈D,f=0
  · left
    apply le_antisymm
    · intro f hf
      simpa only [hall f hf] using (Submodule.zero_mem (⊥ : Submodule (ZMod 2) (ι → ZMod 2)))
    · exact bot_le
  simp only [not_forall,not_imp] at hall
  obtain ⟨h,hh,hh0⟩ := hall
  right
  refine ⟨h,hh,hh0,?_⟩
  by_cases hone : ∀ f∈D,f=0 ∨ f=h
  · exact Or.inl (binary_singleton_span D hh hone)
  simp only [not_forall,not_imp,not_or] at hone
  obtain ⟨g,hg,hg0,hgh⟩ := hone
  have hhg : h≠g := Ne.symm hgh
  exact Or.inr ⟨g,hg,hg0,hhg,
    binary_pair_span D hh hg (constant_weight_four_words hι D hw hh hg hh0 hg0 hhg)⟩

end EntropyDesigns.QuadraticRefinement
