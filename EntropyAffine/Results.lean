/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyAffine.Selected
public import EntropyAffine.Budget
public import EntropyCubic.Weight
public import EntropyCubic.AffineRestriction
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

theorem selected_intrinsic_affine_array_budget {N r : ℕ} (hres : N%8=4)
    (hr : r<N-2) (hgap : N<2^r) (labels : Fin N → Finset (Fin r))
    (hinj : Function.Injective labels) (rows : Fin N → Fin (N-1) → Bool)
    (hOA : IsBinaryStrengthTwo rows) (f : Fin (N-1) → (Finset (Fin r) → ZMod 2))
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i)
    (I : Finset (Fin (N-1))) (hAffine : ∀ i∈I,HasAffineSeedExtension labels (f i)) :
    I.card≤min r (2^r-N-1) := by
  classical
  have hChoice : ∀ i : I,∃ q∈lowDegreeBooleanCode r 1,∀ j,q (labels j)=f i.val (labels j) :=
    fun i => hAffine i.val i.property
  choose q hqC hqValue using hChoice
  let G : Fin (N-1) → (Finset (Fin r) → ZMod 2) :=
    fun i => if hi : i∈I then q ⟨i,hi⟩ else f i
  have hGC : ∀ i∈I,G i∈lowDegreeBooleanCode r 1 := by
    intro i hi
    simpa only [G,dif_pos hi] using hqC ⟨i,hi⟩
  have hGValue : ∀ i j,G i (labels j)=binaryObservationMatrix rows j i := by
    intro i j
    by_cases hi : i∈I
    · simpa only [G,dif_pos hi] using (hqValue ⟨i,hi⟩ j).trans (hmatch i j)
    · simpa only [G,dif_neg hi] using hmatch i j
  have hRank := selected_affine_full_array_rank_bound hres hr labels hinj rows hOA G hGValue I hGC
  let labelB : Fin N → (Fin r → Bool) := fun j => (boolSupportEquiv r).symm (labels j)
  have hB : Function.Injective labelB := (boolSupportEquiv r).symm.injective.comp hinj
  let S : Finset (Fin r → Bool) := Finset.univ.image labelB
  have hcard : S.card=N := by simp [S,Finset.card_image_of_injective _ hB]
  have hS : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hproper : S≠Finset.univ := by
    intro h
    have hh := congrArg Finset.card h
    rw [hcard,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hh
    omega
  let eI : Fin I.card ≃ I := Fintype.equivOfCardEq (by simp)
  let gI : Fin I.card → (Finset (Fin r) → ZMod 2) := fun i => G (eI i).val
  have hI : ∀ i,gI i∈lowDegreeBooleanCode r 1 := fun i => hGC (eI i).val (eI i).property
  have hLabels (j : Fin N) : boolCoordinateSupport (labelB j)=labels j := by
    change (boolSupportEquiv r) ((boolSupportEquiv r).symm (labels j))=labels j
    exact (boolSupportEquiv r).apply_symm_apply _
  have hValue (i : Fin I.card) (j : Fin N) :
      (booleanValueSign (gI i (boolCoordinateSupport (labelB j))) : ℝ)=
        (bitSign (rows j (eI i).val) : ℝ) := by
    rw [hLabels]
    change (booleanValueSign (G (eI i).val (labels j)) : ℝ)=_
    rw [hGValue]
    cases hb : rows j (eI i).val <;>
      norm_num [binaryObservationMatrix,booleanValueSign,bitSign,hb]
  have hsum (v : (Fin r → Bool) → ℝ) : (∑ x∈S,v x)=∑ j : Fin N,v (labelB j) := by
    exact Finset.sum_image (fun a _ b _ h => hB h)
  have hMom := strength_two_all_moments (by omega : 2≤N-1) rows hOA
  have hmean : ∀ i,∑ x∈S,(booleanValueSign (gI i (boolCoordinateSupport x)) : ℝ)=0 := by
    intro i
    rw [hsum]
    simp_rw [hValue]
    exact_mod_cast hMom.1 (eI i).val
  have hpair : ∀ i j,i≠j → ∑ x∈S,
      (booleanValueSign (gI i (boolCoordinateSupport x)) : ℝ)*
        (booleanValueSign (gI j (boolCoordinateSupport x)) : ℝ)=0 := by
    intro i j hij
    have hne : (eI i).val≠(eI j).val := by
      intro h
      exact hij (eI.injective (Subtype.ext h))
    rw [hsum]
    simp_rw [hValue]
    exact_mod_cast hMom.2 (eI i).val (eI j).val hne
  have hComp := affine_unbiased_output_complement_budget S hS hproper gI hI hmean hpair
  rw [hcard] at hComp
  have hNat : ∀ a b : ℕ,a+1≤b → a≤b-1 := by omega
  exact le_min hRank (hNat _ _ hComp)

open scoped Classical in
def affineSeedColumnSet {N m r : ℕ} (labels : Fin N → Finset (Fin r))
    (f : Fin m → (Finset (Fin r) → ZMod 2)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => HasAffineSeedExtension labels (f i))

theorem affine_hadamard_seed_observable_budget {d r : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1)
    (hres : (d+1)%8=4) (hr : r<(d+1)-2) (hgap : d+1<2^r)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (f : Fin d → (Finset (Fin r) → ZMod 2))
    (hmatch : ∀ j i,booleanValueSign (f i (labels j))=H j i.succ) :
    (affineSeedColumnSet labels f).card≤min r (2^r-(d+1)-1) := by
  classical
  let rows := integerHadamardTruthRows H
  have hOA := integerHadamardTruthRows_strength_two hH hzero
  have hValues : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i := by
    intro i j
    apply booleanValueSign_injective
    exact (hmatch j i).trans (integerHadamardTruthRows_binary_value hH j i).symm
  apply selected_intrinsic_affine_array_budget hres hr hgap labels hinj rows hOA f hValues
    (affineSeedColumnSet labels f)
  intro i hi
  exact (Finset.mem_filter.mp hi).2

theorem twelve_seed_nonaffine_budget
    (H : Matrix (Fin 12) (Fin 12) ℤ) (hH : Matrix.IsHadamard H) (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ 11⟩=1)
    (labels : Fin 12 → Finset (Fin 4)) (hinj : Function.Injective labels)
    (f : Fin 11 → (Finset (Fin 4) → ZMod 2))
    (hmatch : ∀ j i,booleanValueSign (f i (labels j))=H j i.succ) :
    (affineSeedColumnSet labels f).card≤3 ∧ 8≤11-(affineSeedColumnSet labels f).card := by
  have hh := affine_hadamard_seed_observable_budget (d:=11) (r:=4) H hH hzero
    (by decide) (by decide) (by decide) labels hinj f hmatch
  norm_num at hh
  omega

theorem twenty_seed_nonaffine_budget
    (H : Matrix (Fin 20) (Fin 20) ℤ) (hH : Matrix.IsHadamard H) (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ 19⟩=1)
    (labels : Fin 20 → Finset (Fin 5)) (hinj : Function.Injective labels)
    (f : Fin 19 → (Finset (Fin 5) → ZMod 2))
    (hmatch : ∀ j i,booleanValueSign (f i (labels j))=H j i.succ) :
    (affineSeedColumnSet labels f).card≤5 ∧ 14≤19-(affineSeedColumnSet labels f).card := by
  have hh := affine_hadamard_seed_observable_budget (d:=19) (r:=5) H hH hzero
    (by decide) (by decide) (by decide) labels hinj f hmatch
  norm_num at hh
  omega

end
end EntropyDesigns
