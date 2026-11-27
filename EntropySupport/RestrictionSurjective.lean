/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.EvenRestriction
public import EntropyAffine.Indicator
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem full_binary_array_submodule_dichotomy {N : ℕ} (hN : 4≤N) (hres : N%8=4)
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (C : Submodule (ZMod 2) (Fin N → ZMod 2))
    (hC : ∀ i,augmentedBinaryColumns rows i∈C) :
    C=⊤ ∨ ∀ g∈C,(∑ j,g j)=0 := by
  classical
  by_cases ht : C=⊤
  · exact Or.inl ht
  right
  let F := augmentedBinaryColumns rows
  have hi : LinearIndependent (ZMod 2) F :=
    binary_pairwise_augmented_independent (by omega) hres (by omega) rows hOA
  have hdim : Module.finrank (ZMod 2) C<N := by
    have hh := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr ht)
    simpa using hh
  have hspan : Submodule.span (ZMod 2) (Set.range F)=C := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hC i
    · rw [finrank_span_eq_card hi]
      simp only [Fintype.card_option,Fintype.card_fin]
      omega
  have hzero : ∀ i,(∑ j,F i j)=0 := by
    intro i
    cases i with
    | none =>
      change (∑ j : Fin N,(1 : ZMod 2))=0
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      exact (ZMod.natCast_eq_natCast_iff' N 0 2).mpr (by omega)
    | some i => exact binary_pairwise_column_sum (by omega) hres rows hOA i
  intro g hg
  rw [← hspan] at hg
  induction hg using Submodule.span_induction with
  | mem g hg => obtain ⟨i,rfl⟩ := hg; exact hzero i
  | zero => simp
  | add f g hf hg ihf ihg => simpa [Finset.sum_add_distrib,ihf,ihg]
  | smul c f hf ih =>
    change (∑ j,c*f j)=0
    rw [← Finset.mul_sum,ih,mul_zero]

theorem residue_four_encoded_restriction_surjective {N r : ℕ}
    (hN : 4≤N) (hr : 4≤r) (hres : N%8=4)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels)
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-2) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) :
    ∀ v : Fin N → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-2),
      binaryLabelEvaluation labels g=v := by
  classical
  let C := (lowDegreeBooleanCode r (r-2)).map (binaryLabelEvaluation labels)
  have hC : ∀ i,augmentedBinaryColumns rows i∈C := by
    intro i
    cases i with
    | none =>
      refine Submodule.mem_map.mpr ⟨fun _ => 1,lowDegreeBooleanCode_one_mem r (r-2),?_⟩
      rfl
    | some i =>
      refine Submodule.mem_map.mpr ⟨f i,hf i,?_⟩
      funext j
      exact hmatch i j
  have ht : C=⊤ := by
    rcases full_binary_array_submodule_dichotomy hN hres rows hOA C hC with ht|heven
    · exact ht
    exfalso
    have hp : ∀ g∈lowDegreeBooleanCode r (r-2),(∑ j,g (labels j))=0 := by
      intro g hg
      exact heven _ (Submodule.mem_map.mpr ⟨g,hg,rfl⟩)
    have hdual := label_support_indicator_dual (r:=r) (d:=r-2) (by omega) labels hinj hp
    have hd : r-(r-2)-1=1 := by omega
    rw [hd] at hdual
    have hcard : (Finset.univ.image labels).card%8=4 := by
      simpa [Finset.card_image_of_injective _ hinj] using hres
    exact residue_four_support_indicator_not_affine hr _ hcard hdual
  intro v
  have hv : v∈C := by rw [ht]; trivial
  exact Submodule.mem_map.mp hv

end
end EntropyDesigns
