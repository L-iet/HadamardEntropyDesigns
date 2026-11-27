/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPermutationCost.CentralOccupation
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.Powerset
@[expose] public section
namespace EntropyDesigns.PermutationCost

noncomputable def patternMultiplicity {N d : ℕ} (rows : Fin N → Fin d → Bool)
    (x : Fin d → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r => rows r=x)).card

def IsFullyPermutationSymmetric {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop :=
  ∀ (σ : Equiv.Perm (Fin d)) (x : Fin d → Bool),
    patternMultiplicity rows (fun i => x (σ i))=patternMultiplicity rows x

 theorem equal_weight_permutation {d : ℕ} (x y : Fin d → Bool)
    (hw : hammingWeight x=hammingWeight y) :
    ∃ σ : Equiv.Perm (Fin d),∀ i,y (σ i)=x i := by
  classical
  have hc (b : Bool) : Fintype.card {i : Fin d // x i=b}=
      Fintype.card {i : Fin d // y i=b} := by
    cases b with
    | true => simpa [Fintype.subtype_card,hammingWeight] using hw
    | false =>
      have hx : Fintype.card {i : Fin d // x i=false}=d-hammingWeight x := by
        simpa [Fintype.subtype_card,hammingWeight,Finset.filter_not,
          ←Bool.not_eq_true] using Fintype.card_subtype_compl (fun i => x i=true)
      have hy : Fintype.card {i : Fin d // y i=false}=d-hammingWeight y := by
        simpa [Fintype.subtype_card,hammingWeight,Finset.filter_not,
          ←Bool.not_eq_true] using Fintype.card_subtype_compl (fun i => y i=true)
      rw [hx,hy,hw]
  let e (b : Bool) := Fintype.equivOfCardEq (hc b)
  exact ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩

 theorem same_weight_multiplicity {N d : ℕ} (rows : Fin N → Fin d → Bool)
    (hsym : IsFullyPermutationSymmetric rows) (x y : Fin d → Bool)
    (hw : hammingWeight x=hammingWeight y) :
    patternMultiplicity rows x=patternMultiplicity rows y := by
  obtain ⟨σ,hσ⟩ := equal_weight_permutation x y hw
  have he : (fun i => y (σ i))=x := funext hσ
  simpa only [he] using hsym σ y

noncomputable def booleanSupport {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter (fun i => x i=true)

 theorem boolean_support_injective (d : ℕ) :
    Function.Injective (@booleanSupport d) := by
  classical
  intro x y he
  funext i
  have hm : x i=true ↔ y i=true := by
    simpa [booleanSupport] using (Finset.ext_iff.mp he i)
  cases hx : x i <;> cases hy : y i <;> simp_all

 theorem weight_layer_card (d k : ℕ) :
    (Finset.univ.filter (fun x : Fin d → Bool => hammingWeight x=k)).card=d.choose k := by
  classical
  let S := Finset.univ.filter (fun x : Fin d → Bool => hammingWeight x=k)
  have he : S.image booleanSupport=Finset.univ.powersetCard k := by
    ext t
    simp only [S,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_powersetCard,Finset.subset_univ,and_true]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro ht
      let x : Fin d → Bool := fun i => decide (i∈t)
      have hx : booleanSupport x=t := by ext i;simp [booleanSupport,x]
      refine ⟨x,?_,hx⟩
      change (booleanSupport x).card=k
      rw [hx]
      exact ht
  calc
    _=(S.image booleanSupport).card :=
      (Finset.card_image_of_injective S (boolean_support_injective d)).symm
    _=(Finset.univ.powersetCard k).card := congrArg Finset.card he
    _=d.choose k := by simp

 theorem occupied_weight_binomial_run_bound {N d : ℕ}
    (rows : Fin N → Fin d → Bool) (hsym : IsFullyPermutationSymmetric rows)
    (r : Fin N) : d.choose (hammingWeight (rows r))≤N := by
  classical
  let k := hammingWeight (rows r)
  have hpos : 0<patternMultiplicity rows (rows r) := by
    apply Finset.card_pos.mpr
    exact ⟨r,by simp⟩
  have hex (y : {y : Fin d → Bool // hammingWeight y=k}) :
      ∃ s : Fin N,rows s=y.val := by
    have hm := same_weight_multiplicity rows hsym (rows r) y.val y.property.symm
    have hy : 0<patternMultiplicity rows y.val := by omega
    obtain ⟨s,hs⟩ := Finset.card_pos.mp hy
    exact ⟨s,(Finset.mem_filter.mp hs).2⟩
  choose f hf using hex
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact (hf x).symm.trans ((congrArg rows he).trans (hf y))
  have hcard : Fintype.card {y : Fin d → Bool // hammingWeight y=k}=d.choose k := by
    simpa only [Fintype.subtype_card] using weight_layer_card d k
  have hb := Fintype.card_le_of_injective f hi
  simpa only [hcard,Fintype.card_fin] using hb

 theorem permutation_symmetric_central_layer_bound {N d : ℕ} (hd : 2≤d) (hN : 0<N)
    (rows : Fin N → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows)
    (hsym : IsFullyPermutationSymmetric rows) :
    ∃ k : ℕ,k≤d ∧ (2*(k:ℝ)-(d:ℝ))^2≤(d:ℝ) ∧ d.choose k≤N := by
  obtain ⟨r,hr⟩ := occupied_central_weight hd hN rows hOA
  refine ⟨hammingWeight (rows r),?_,hr,occupied_weight_binomial_run_bound rows hsym r⟩
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin d)

end EntropyDesigns.PermutationCost
