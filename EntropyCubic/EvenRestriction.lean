/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Weight
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def binarySeedParity {N r : ℕ} (labels : Fin N → Finset (Fin r)) :
    (Finset (Fin r) → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun g := ∑ j,g (labels j)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

theorem encoded_full_dimension_code_even {N r d : ℕ} (hN : 12≤N) (hres : N%8=4)
    (labels : Fin N → Finset (Fin r))
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-2) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r d)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i)
    (hdim : Module.finrank (ZMod 2) (lowDegreeBooleanCode r d)=N-1) :
    ∀ g∈lowDegreeBooleanCode r d,(∑ j,g (labels j))=0 := by
  classical
  let F : Option (Fin (N-2)) → (Finset (Fin r) → ZMod 2) :=
    fun i => Option.elim i (fun _ => 1) f
  have hFC : ∀ i,F i∈lowDegreeBooleanCode r d := by
    intro i
    cases i with
    | none => exact lowDegreeBooleanCode_one_mem r d
    | some i => exact hf i
  have hi : LinearIndependent (ZMod 2) F := by
    apply LinearIndependent.of_comp (binaryLabelEvaluation labels)
    have he : binaryLabelEvaluation labels ∘ F=augmentedBinaryColumns rows := by
      funext i j
      cases i with
      | none => rfl
      | some i => exact hmatch i j
    rw [he]
    exact binary_pairwise_augmented_independent (by omega) hres (by omega) rows hOA
  have hspan : Submodule.span (ZMod 2) (Set.range F)=lowDegreeBooleanCode r d := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hFC i
    · rw [hdim,finrank_span_eq_card hi]
      simp only [Fintype.card_option,Fintype.card_fin]
      omega
  have hzero : ∀ i,binarySeedParity labels (F i)=0 := by
    intro i
    cases i with
    | none =>
      change (∑ j : Fin N,(1 : ZMod 2))=0
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      exact (ZMod.natCast_eq_natCast_iff' N 0 2).mpr (by omega)
    | some i =>
      change (∑ j,f i (labels j))=0
      simp_rw [hmatch]
      exact binary_pairwise_column_sum (by omega) hres rows hOA i
  have hker : lowDegreeBooleanCode r d≤(binarySeedParity labels).ker := by
    rw [←hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hzero i
  intro g hg
  exact hker hg

theorem label_support_indicator_dual {N r d : ℕ} (hd : d<r)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels)
    (hparity : ∀ g∈lowDegreeBooleanCode r d,(∑ j,g (labels j))=0) :
    booleanSupportIndicator (Finset.univ.image labels)∈lowDegreeBooleanCode r (r-d-1) := by
  classical
  rw [←lowDegreeBooleanCode_duality hd]
  intro g hg
  change (∑ z : Finset (Fin r),g z*booleanSupportIndicator (Finset.univ.image labels) z)=0
  let S := Finset.univ.image labels
  have heq : (∑ z : Finset (Fin r),g z*booleanSupportIndicator S z)=∑ j,g (labels j) := by
    calc
      _=∑ z∈S,g z*booleanSupportIndicator S z := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro z _ hz
        simp [booleanSupportIndicator,hz]
      _=∑ z∈S,g z := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [booleanSupportIndicator,hz]
      _=∑ j,g (labels j) := by
        exact Finset.sum_image (fun a _ b _ h => hinj h)
  exact heq.trans (hparity g hg)

theorem quadratics_four_bit_dimension : Module.finrank (ZMod 2) (lowDegreeBooleanCode 4 2)=11 := by
  rw [lowDegreeBooleanCode_finrank]
  decide

theorem order_twelve_quadratic_encoding_impossible
    (labels : Fin 12 → Finset (Fin 4)) (hinj : Function.Injective labels)
    (rows : Fin 12 → Fin 10 → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin 10 → (Finset (Fin 4) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode 4 2)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) : False := by
  have hp := encoded_full_dimension_code_even (N:=12) (r:=4) (d:=2)
    (by omega) (by decide) labels rows hOA f hf hmatch quadratics_four_bit_dimension
  have hdual := label_support_indicator_dual (r:=4) (d:=2) (by omega) labels hinj hp
  have hcard : (Finset.univ.image labels).card=12 := by
    simp [Finset.card_image_of_injective _ hinj]
  exact twelve_label_indicator_not_affine (Finset.univ.image labels) hcard hdual

end
end EntropyDesigns
