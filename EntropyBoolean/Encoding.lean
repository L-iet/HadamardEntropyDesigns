/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyBoolean.ArrayRank
public import EntropyBoolean.Dimension
@[expose] public section
namespace EntropyDesigns
noncomputable section

def binaryLabelEvaluation {N r : ℕ} (labels : Fin N → Finset (Fin r)) :
    (Finset (Fin r) → ZMod 2) →ₗ[ZMod 2] (Fin N → ZMod 2) where
  toFun f := fun j => f (labels j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lowDegreeBooleanCode_one_mem (r d : ℕ) :
    (fun _ : Finset (Fin r) => (1 : ZMod 2)) ∈ lowDegreeBooleanCode r d := by
  have hgen : squarefreeBooleanMonomial (∅ : Finset (Fin r)) ∈ lowDegreeBooleanCode r d := by
    apply Submodule.subset_span
    exact ⟨⟨∅,by simp⟩,rfl⟩
  have heq : squarefreeBooleanMonomial (∅ : Finset (Fin r))=(fun _ => (1 : ZMod 2)) := by
    funext z
    simp [squarefreeBooleanMonomial]
  rwa [heq] at hgen

theorem minimal_binary_seed_bounds {N r : ℕ} (hN : 12≤N) (hres : N%8=4)
    (hlo : 2^(r-1)<N) (hhi : N≤2^r) :
    4≤r ∧ 2^(r-1)<N-1 ∧ N<2^r := by
  have hr : 4≤r := by
    by_contra h
    have hh : r≤3 := by omega
    interval_cases r <;> norm_num at hhi <;> omega
  have hp : 2^(r-1)=2*2^(r-2) := by
    have he : r-1=(r-2)+1 := by omega
    rw [he,Nat.pow_succ]
    omega
  have hlo' : 2^(r-1)<N-1 := by
    have heven : N%2=0 := by omega
    have hhalf : 2^(r-1)%2=0 := by rw [hp]; omega
    generalize hv : 2^(r-1)=v at hlo hhalf ⊢
    omega
  have h8 : 8∣2^r := by
    have he : r=3+(r-3) := by omega
    rw [he,pow_add]
    norm_num
  have hupper : N<2^r := by
    by_contra h
    have he : N=2^r := by omega
    have hm : N%8=0 := Nat.mod_eq_zero_of_dvd (he ▸ h8)
    omega
  exact ⟨hr,hlo',hupper⟩

theorem encoded_binary_pairwise_degree_lower {N r d : ℕ}
    (hN : 12≤N) (hres : N%8=4) (hlo : 2^(r-1)<N) (hhi : N≤2^r)
    (labels : Fin N → Finset (Fin r))
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-2) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r d)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) : r≤2*d := by
  classical
  obtain ⟨hr,hM,_⟩ := minimal_binary_seed_bounds hN hres hlo hhi
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
  let e : Fin (N-1) ≃ Option (Fin (N-2)) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin,Fintype.card_option]
    omega)
  apply lowDegreeBooleanCode_degree_of_independent_family (r:=r) (d:=d) (M:=N-1)
    (by omega) hM (F ∘ e) (fun i => hFC (e i))
  exact hi.comp e e.injective

theorem minimal_binary_seed_extension_upper {N r : ℕ}
    (hN : 12≤N) (hres : N%8=4) (hlo : 2^(r-1)<N) (hhi : N≤2^r)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels) :
    ∀ y : Fin N → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-1), ∀ j,g (labels j)=y j := by
  classical
  obtain ⟨hr,_,hupper⟩ := minimal_binary_seed_bounds hN hres hlo hhi
  let S : Finset (Finset (Fin r)) := Finset.univ.image labels
  have hcard : S.card=N := by simp [S,Finset.card_image_of_injective _ hinj]
  have hproper : S≠Finset.univ := by
    intro heq
    have hh := congrArg Finset.card heq
    rw [hcard,Finset.card_univ,Fintype.card_finset,Fintype.card_fin] at hh
    omega
  intro y
  let f : S → ZMod 2 := fun z => Function.extend labels y (fun _ => 0) z.val
  obtain ⟨g,hg,hgf⟩ := properBooleanSupport_degree_pred_extension (by omega) S hproper f
  refine ⟨g,hg,?_⟩
  intro j
  have hmem : labels j∈S := Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hh := congrFun hgf (⟨labels j,hmem⟩ : S)
  change g (labels j)=Function.extend labels y (fun _ => 0) (labels j) at hh
  exact hh.trans (hinj.extend_apply y (fun _ => 0) j)

theorem minimal_binary_seed_growing_degree {N r d : ℕ}
    (hN : 12≤N) (hres : N%8=4) (hlo : 2^(r-1)<N) (hhi : N≤2^r)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels)
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-2) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r d)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) :
    r≤2*d ∧ (∀ y : Fin N → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-1), ∀ j,g (labels j)=y j) := by
  exact ⟨encoded_binary_pairwise_degree_lower hN hres hlo hhi labels rows hOA f hf hmatch,
    minimal_binary_seed_extension_upper hN hres hlo hhi labels hinj⟩

end
end EntropyDesigns
