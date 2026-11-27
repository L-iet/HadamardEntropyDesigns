/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean
@[expose] public section
namespace EntropyDesigns
noncomputable section

def affineBooleanMonomialFamily (r : ℕ) : Option (Fin r) → (Finset (Fin r) → ZMod 2) :=
  fun i => Option.elim i (squarefreeBooleanMonomial ∅) (fun j => squarefreeBooleanMonomial {j})

theorem degree_one_boolean_code_dimension_le (r : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode r 1)≤r+1 := by
  have hspan : lowDegreeBooleanCode r 1≤
      Submodule.span (ZMod 2) (Set.range (affineBooleanMonomialFamily r)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    change squarefreeBooleanMonomial s.val ∈ _
    by_cases hs : s.val=∅
    · rw [hs]
      exact Submodule.subset_span ⟨none,rfl⟩
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have he : s.val={i} := by
        ext j
        simp only [Finset.mem_singleton]
        constructor
        · intro hj
          exact Finset.card_le_one.mp s.property j hj i hi
        · intro hj; subst j; exact hi
      rw [he]
      exact Submodule.subset_span ⟨some i,rfl⟩
  have hc : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (affineBooleanMonomialFamily r)))≤r+1 := by
    simpa only [Set.finrank,Fintype.card_option,Fintype.card_fin] using
      (finrank_range_le_card (R:=ZMod 2) (affineBooleanMonomialFamily r))
  exact (Submodule.finrank_mono hspan).trans hc

theorem encoded_even_binary_code_rank {N r k d : ℕ} (hk : 2≤k) (hres : N%8=4)
    (hkeven : k%2=0) (labels : Fin N → Finset (Fin r))
    (rows : Fin N → Fin k → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin k → (Finset (Fin r) → ZMod 2)) (hf : ∀ i,f i∈lowDegreeBooleanCode r d)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) :
    k+1≤Module.finrank (ZMod 2) (lowDegreeBooleanCode r d) := by
  let F : Option (Fin k) → (Finset (Fin r) → ZMod 2) := fun i => Option.elim i (fun _ => 1) f
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
    exact binary_pairwise_augmented_independent hk hres hkeven rows hOA
  let FC : Option (Fin k) → lowDegreeBooleanCode r d := fun i => ⟨F i,hFC i⟩
  have hiC : LinearIndependent (ZMod 2) FC := by
    apply LinearIndependent.of_comp (lowDegreeBooleanCode r d).subtype
    exact hi
  have hc := hiC.fintype_card_le_finrank
  simpa only [Fintype.card_option,Fintype.card_fin] using hc

theorem affine_even_binary_output_bound {N r k : ℕ} (hk : 2≤k) (hres : N%8=4)
    (hkeven : k%2=0) (labels : Fin N → Finset (Fin r))
    (rows : Fin N → Fin k → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin k → (Finset (Fin r) → ZMod 2)) (hf : ∀ i,f i∈lowDegreeBooleanCode r 1)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) : k≤r := by
  have hh := encoded_even_binary_code_rank hk hres hkeven labels rows hOA f hf hmatch
  have hc := degree_one_boolean_code_dimension_le r
  omega

theorem twenty_label_six_affine_outputs_impossible
    (labels : Fin 20 → Finset (Fin 5))
    (rows : Fin 20 → Fin 6 → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin 6 → (Finset (Fin 5) → ZMod 2)) (hf : ∀ i,f i∈lowDegreeBooleanCode 5 1)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) : False := by
  have hh := affine_even_binary_output_bound (by omega) (by decide) (by decide) labels rows hOA f hf hmatch
  omega

theorem affineBooleanMonomialFamily_linearIndependent (r : ℕ) :
    LinearIndependent (ZMod 2) (affineBooleanMonomialFamily r) := by
  classical
  let θ : Option (Fin r) → Finset (Fin r) := fun i => Option.elim i ∅ (fun j => {j})
  have hθ : Function.Injective θ := by
    intro a b hab
    cases a <;> cases b <;> simp_all [θ]
  have hi := (squarefreeBooleanMonomial_linearIndependent (ι:=Fin r)).comp θ hθ
  have heq : (fun i : Option (Fin r) => squarefreeBooleanMonomial (θ i))=affineBooleanMonomialFamily r := by
    funext i
    cases i <;> rfl
  change LinearIndependent (ZMod 2) (fun i : Option (Fin r) => squarefreeBooleanMonomial (θ i)) at hi
  rw [heq] at hi
  exact hi

theorem degree_one_boolean_code_dimension (r : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode r 1)=r+1 := by
  classical
  have hmem : ∀ i,affineBooleanMonomialFamily r i∈lowDegreeBooleanCode r 1 := by
    intro i
    cases i with
    | none =>
      change squarefreeBooleanMonomial (∅ : Finset (Fin r))∈lowDegreeBooleanCode r 1
      exact Submodule.subset_span ⟨⟨∅,by simp⟩,rfl⟩
    | some i =>
      change squarefreeBooleanMonomial {i}∈lowDegreeBooleanCode r 1
      exact Submodule.subset_span ⟨⟨{i},by simp⟩,rfl⟩
  have hspan : Submodule.span (ZMod 2) (Set.range (affineBooleanMonomialFamily r))≤lowDegreeBooleanCode r 1 := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hmem i
  have hlow : r+1≤Module.finrank (ZMod 2) (lowDegreeBooleanCode r 1) := by
    have hh := Submodule.finrank_mono hspan
    rw [finrank_span_eq_card (affineBooleanMonomialFamily_linearIndependent r)] at hh
    simpa only [Fintype.card_option,Fintype.card_fin] using hh
  exact le_antisymm (degree_one_boolean_code_dimension_le r) hlow

end
end EntropyDesigns
