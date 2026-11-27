/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyAffine.Rank
public import EntropyCubic.LowerBounds
@[expose] public section
namespace EntropyDesigns
noncomputable section

theorem encoded_selected_code_dimension {N m r d : ℕ} (hres : N%8=4)
    (labels : Fin N → Finset (Fin r)) (rows : Fin N → Fin m → Bool)
    (hOA : IsBinaryStrengthTwo rows) (f : Fin m → (Finset (Fin r) → ZMod 2))
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i)
    (I E : Finset (Fin m)) (hIE : I⊆E) (hE : 2≤E.card) (heven : E.card%2=0)
    (hf : ∀ i∈I,f i∈lowDegreeBooleanCode r d) :
    I.card+1≤Module.finrank (ZMod 2) (lowDegreeBooleanCode r d) := by
  classical
  let eE : Fin E.card ≃ E := Fintype.equivOfCardEq (by simp)
  let eI : Fin I.card ≃ I := Fintype.equivOfCardEq (by simp)
  let jE : Fin E.card ↪ Fin m := ⟨fun i => (eE i).val,Subtype.val_injective.comp eE.injective⟩
  let rowsE : Fin N → Fin E.card → Bool := fun j i => rows j (jE i)
  have hOAE : IsBinaryStrengthTwo rowsE := binary_strength_two_restrict rows hOA jE
  let FE : Option (Fin E.card) → (Finset (Fin r) → ZMod 2) :=
    fun i => Option.elim i (fun _ => 1) (fun k => f (eE k).val)
  have hiE : LinearIndependent (ZMod 2) FE := by
    apply LinearIndependent.of_comp (binaryLabelEvaluation labels)
    have he : binaryLabelEvaluation labels ∘ FE=augmentedBinaryColumns rowsE := by
      funext i j
      cases i with
      | none => rfl
      | some i => exact hmatch (eE i).val j
    rw [he]
    exact binary_pairwise_augmented_independent hE hres heven rowsE hOAE
  let k : Fin I.card → Fin E.card := fun i => eE.symm ⟨(eI i).val,hIE (eI i).property⟩
  have hk : Function.Injective k := by
    intro i j hij
    apply eI.injective
    apply Subtype.ext
    have hh := congrArg (fun x : Fin E.card => (eE x).val) hij
    simpa [k] using hh
  have hmap : Function.Injective (Option.map k) := by
    intro a b hab
    cases a with
    | none => cases b with
      | none => rfl
      | some b => cases hab
    | some a => cases b with
      | none => cases hab
      | some b => exact congrArg some (hk (Option.some.inj hab))
  let FI : Option (Fin I.card) → (Finset (Fin r) → ZMod 2) :=
    fun i => Option.elim i (fun _ => 1) (fun k => f (eI k).val)
  have heq : FE ∘ Option.map k=FI := by
    funext i
    cases i <;> simp [FE,FI,k]
  have hiI : LinearIndependent (ZMod 2) FI := by
    rw [←heq]
    exact hiE.comp (Option.map k) hmap
  have hFC : ∀ i,FI i∈lowDegreeBooleanCode r d := by
    intro i
    cases i with
    | none => exact lowDegreeBooleanCode_one_mem r d
    | some i => exact hf (eI i).val (eI i).property
  let FIC : Option (Fin I.card) → lowDegreeBooleanCode r d := fun i => ⟨FI i,hFC i⟩
  have hiC : LinearIndependent (ZMod 2) FIC := by
    apply LinearIndependent.of_comp (lowDegreeBooleanCode r d).subtype
    exact hiI
  have hc := hiC.fintype_card_le_finrank
  simpa only [Fintype.card_option,Fintype.card_fin] using hc

theorem selected_affine_full_array_rank_bound {N r : ℕ} (hres : N%8=4) (hr : r<N-2)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels)
    (rows : Fin N → Fin (N-1) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-1) → (Finset (Fin r) → ZMod 2))
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i)
    (I : Finset (Fin (N-1))) (hf : ∀ i∈I,f i∈lowDegreeBooleanCode r 1) : I.card≤r := by
  classical
  have hN : 4≤N := by omega
  have hcard : N≤2^r := by
    have hh := Fintype.card_le_of_injective labels hinj
    simpa only [Fintype.card_fin,Fintype.card_finset] using hh
  have hrpos : 1≤r := by
    by_contra h
    have hz : r=0 := by omega
    rw [hz] at hcard
    norm_num at hcard
    omega
  by_cases hsmall : I.card≤1
  · omega
  have hlarge : 2≤I.card := by omega
  have hproper : I≠Finset.univ := by
    intro heq
    let j : Fin (N-1) := ⟨0,by omega⟩
    let E : Finset (Fin (N-1)) := Finset.univ.erase j
    have hEcard : E.card=N-2 := by simp [E,Nat.sub_sub]
    have hh := encoded_selected_code_dimension hres labels rows hOA f hmatch E E
      (fun _ h => h) (by rw [hEcard]; omega) (by rw [hEcard]; omega)
      (by intro i _; apply hf i; rw [heq]; exact Finset.mem_univ _)
    have hc := degree_one_boolean_code_dimension_le r
    rw [hEcard] at hh
    omega
  by_cases heven : I.card%2=0
  · have hh := encoded_selected_code_dimension hres labels rows hOA f hmatch I I
      (fun _ h => h) hlarge heven hf
    have hc := degree_one_boolean_code_dimension_le r
    omega
  · have hex : ∃ j : Fin (N-1),j∉I := by
      by_contra! h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨j,hj⟩ := hex
    let E := insert j I
    have hEcard : E.card=I.card+1 := Finset.card_insert_of_notMem hj
    have hh := encoded_selected_code_dimension hres labels rows hOA f hmatch I E
      (by intro i hi; exact Finset.mem_insert_of_mem hi)
      (by rw [hEcard]; omega) (by rw [hEcard]; omega) hf
    have hc := degree_one_boolean_code_dimension_le r
    omega

end
end EntropyDesigns
