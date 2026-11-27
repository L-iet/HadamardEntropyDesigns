/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.BinaryRank
public import EntropyDesigns.MinimalSupport
public import EntropyDesigns.SupportRestriction
public import EntropyDesigns.BinaryHyperplanes
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
@[expose] public section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EntropyDesigns

noncomputable def uniformFiniteLaw {α : Type*} [DecidableEq α] (S : Finset α) (x : α) : ℝ :=
  if x∈S then 1/(S.card : ℝ) else 0

noncomputable def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1/2 : ℝ)*(∑ x,|p x-q x|)

theorem uniformFiniteLaw_mass {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : 0<S.card) : (∑ x,uniformFiniteLaw S x)=1 := by
  have hne : (S.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : S.card ≠ 0)
  simp [uniformFiniteLaw,Finset.sum_ite,Finset.sum_const]
  field_simp

theorem uniformFiniteLaw_nonneg {α : Type*} [DecidableEq α] (S : Finset α) (x : α) :
    0≤uniformFiniteLaw S x := by
  unfold uniformFiniteLaw
  split_ifs <;> positivity

theorem uniformFiniteLaw_variation {α : Type*} [Fintype α] [DecidableEq α]
    {N : ℕ} (hN : 0<N) (S T : Finset α) (hS : S.card=N) (hT : T.card=N) :
    totalVariation (uniformFiniteLaw S) (uniformFiniteLaw T)=
      1-((S∩T).card : ℝ)/(N : ℝ) := by
  have hc : (0 : ℝ)≤1/(N : ℝ) := by positivity
  have hpt (x : α) : |uniformFiniteLaw S x-uniformFiniteLaw T x|=
      uniformFiniteLaw S x+uniformFiniteLaw T x-2*(if x∈S∩T then 1/(N : ℝ) else 0) := by
    by_cases hs : x∈S <;> by_cases ht : x∈T <;>
      simp [uniformFiniteLaw,hs,ht,hS,hT,abs_of_nonneg hc] <;> ring
  have hmassS := uniformFiniteLaw_mass S (by omega)
  have hmassT := uniformFiniteLaw_mass T (by omega)
  have hfilter : Finset.univ.filter (fun x : α => x∈S∩T)=S∩T := by ext x; simp
  unfold totalVariation
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hmassS,hmassT,← Finset.mul_sum]
  simp only [Finset.sum_ite,Finset.sum_const,nsmul_eq_mul,hfilter]
  ring

theorem uniform_on_activeSupport {α : Type*} [Fintype α] [DecidableEq α]
    (q : α → ℝ) (N : ℕ) (hcard : (activeSupport q).card=N)
    (huni : ∀ x : activeSupport q,q x=1/(N : ℝ)) : q=uniformFiniteLaw (activeSupport q) := by
  classical
  ext x
  by_cases hx : x∈activeSupport q
  · rw [uniformFiniteLaw,if_pos hx,hcard]
    exact huni ⟨x,hx⟩
  · have hzero : q x=0 := by simpa [activeSupport] using hx
    simp [uniformFiniteLaw,hx,hzero]


noncomputable def codeInsideRows {N d : ℕ} (A : Matrix (Fin N) (Fin d) (ZMod 2))
    (C : Submodule (ZMod 2) (Fin d → ZMod 2)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => A.row i∈C)

noncomputable def codeOutsideRows {N d : ℕ} (A : Matrix (Fin N) (Fin d) (ZMod 2))
    (C : Submodule (ZMod 2) (Fin d → ZMod 2)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => A.row i∉C)

theorem matrix_rank_le_code_plus_outside {N d : ℕ} (A : Matrix (Fin N) (Fin d) (ZMod 2))
    (C : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    Matrix.rank A≤Module.finrank (ZMod 2) C+
      (codeOutsideRows A C).card := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter (fun i => A.row i∉C)
  let B := S.image A.row
  let U : Submodule (ZMod 2) (Fin d → ZMod 2) := Submodule.span (ZMod 2) (B : Set (Fin d → ZMod 2))
  have hspan : Submodule.span (ZMod 2) (Set.range A.row)≤C⊔U := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    by_cases hi : A.row i∈C
    · exact Submodule.mem_sup.mpr ⟨A.row i,hi,0,U.zero_mem,by simp⟩
    · have hU : A.row i∈U := by
        apply Submodule.subset_span
        exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩,rfl⟩
      exact Submodule.mem_sup.mpr ⟨0,C.zero_mem,A.row i,hU,by simp⟩
  have hUrank : Module.finrank (ZMod 2) U≤S.card := by
    have hh : Module.finrank (ZMod 2) U≤B.card := finrank_span_finset_le_card B
    exact hh.trans (Finset.card_image_le)
  change Matrix.rank A≤Module.finrank (ZMod 2) C+S.card
  rw [Matrix.rank_eq_finrank_span_row]
  calc
    _ ≤ Module.finrank (ZMod 2) ↥(C⊔U) := Submodule.finrank_mono hspan
    _ ≤ Module.finrank (ZMod 2) C+Module.finrank (ZMod 2) U := Submodule.finrank_add_le_finrank_add_finrank C U
    _ ≤ _ := Nat.add_le_add_left hUrank _

theorem minimal_target_code_overlap {N r : ℕ} (hN : 12≤N) (hres : N%8=4)
    (rows : Fin N → Fin (N-4) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (C : Submodule (ZMod 2) (Fin (N-4) → ZMod 2))
    (hC : Module.finrank (ZMod 2) C≤r) :
    (codeInsideRows (binaryObservationMatrix rows) C).card≤r+4 := by
  classical
  have hRank := (minimal_target_binary_rank hN hres rows hOA).2
  have hh := matrix_rank_le_code_plus_outside (binaryObservationMatrix rows) C
  rw [hRank] at hh
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin N => (binaryObservationMatrix rows).row i∈C)
  simp only [Finset.card_univ,Fintype.card_fin] at hc
  change (Finset.univ.filter (fun i => (binaryObservationMatrix rows).row i∈C)).card≤r+4
  change N-4≤Module.finrank (ZMod 2) C+(Finset.univ.filter (fun i => (binaryObservationMatrix rows).row i∉C)).card at hh
  omega

theorem minimal_cube_target_uniform {N : ℕ} (hN : 12≤N) (hres : N%8=4)
    (q : (Fin (N-4) → Bool) → ℝ) (hq : ∀ x,0≤q x) (hmass : ∑ x,q x=1)
    (hmean : ∀ i,∑ x,q x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)
    (hcard : (activeSupport q).card≤N) :
    (activeSupport q).card=N ∧ ∀ x : activeSupport q,q x=1/(N : ℝ) := by
  classical
  let S := activeSupport q
  let W : S → ℝ := fun x => q x
  let x : S → Fin (N-4) → ℤ := fun a i => bitSign (a.val i)
  let A := augmentedSign x
  have hs : ∀ a i,x a i=1 ∨ x a i= -1 := fun a i => bitSign_sign (a.val i)
  have hm : (∑ a : S,W a)=1 := by
    calc
      _ = ∑ a,q a := by simpa only [mul_one] using activeSupport_sum q (fun _ => 1)
      _ = 1 := hmass
  have hmean' (i : Fin (N-4)) : (∑ a : S,W a*(x a i : ℝ))=0 := by
    calc
      _ = ∑ a,q a*(bitSign (a i) : ℝ) := activeSupport_sum q (fun a => (bitSign (a i) : ℝ))
      _ = 0 := hmean i
  have hpair' (i j : Fin (N-4)) (hij : i≠j) : (∑ a : S,W a*(x a i : ℝ)*(x a j : ℝ))=0 := by
    calc
      _ = ∑ a,q a*(bitSign (a i) : ℝ)*(bitSign (a j) : ℝ) := by
        simpa only [mul_assoc] using activeSupport_sum q (fun a => (bitSign (a i) : ℝ)*(bitSign (a j) : ℝ))
      _ = 0 := hpair i j hij
  have hr : roundedDimension ((N-4)+1)=N := by unfold roundedDimension; omega
  have hcard' : Fintype.card S≤roundedDimension ((N-4)+1) := by simpa only [S,Fintype.card_coe,hr] using hcard
  have hh := minimal_support_uniform_rigidity (by omega : 3≤(N-4)+1) hcard' A W
    (augmentedSign_sign x hs) (fun a => hq a) hm (augmentedSign_isotropic x W hs hm hmean' hpair')
  exact ⟨by simpa only [S,Fintype.card_coe,hr] using hh.1,by simpa only [hr] using hh.2.1⟩

theorem minimal_cube_target_array {N : ℕ} (hN : 12≤N) (hres : N%8=4)
    (q : (Fin (N-4) → Bool) → ℝ) (hq : ∀ x,0≤q x) (hmass : ∑ x,q x=1)
    (hmean : ∀ i,∑ x,q x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)
    (hcard : (activeSupport q).card≤N) :
    ∃ rows : Fin N → Fin (N-4) → Bool,IsBinaryStrengthTwo rows ∧ Function.Injective rows ∧
      ∀ x,x∈activeSupport q ↔ ∃ r,rows r=x := by
  classical
  obtain ⟨hcard',huni⟩ := minimal_cube_target_uniform hN hres q hq hmass hmean hpair hcard
  let S := activeSupport q
  have hc : Fintype.card S=N := by simpa only [S,Fintype.card_coe] using hcard'
  let e : S ≃ Fin N := (Fintype.equivFin S).trans (finCongr hc)
  let rows : Fin N → Fin (N-4) → Bool := fun r => (e.symm r).val
  have hn : (1/(N : ℝ)) ≠ 0 := by positivity
  have hf (i : Fin (N-4)) : (∑ r,bitSign (rows r i))=0 := by
    have hh : (∑ r : Fin N,(1/(N : ℝ))*(bitSign (rows r i) : ℝ))=0 := by
      calc
        _ = ∑ a : S,(1/(N : ℝ))*(bitSign (a.val i) : ℝ) :=
          Equiv.sum_comp e.symm (fun a : S => (1/(N : ℝ))*(bitSign (a.val i) : ℝ))
        _ = ∑ a : S,q a*(bitSign (a.val i) : ℝ) := by simp only [huni]
        _ = ∑ a,q a*(bitSign (a i) : ℝ) := activeSupport_sum q (fun a => (bitSign (a i) : ℝ))
        _ = 0 := hmean i
    rw [← Finset.mul_sum] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left hn
    exact_mod_cast hz
  have hp (i j : Fin (N-4)) (hij : i≠j) : (∑ r,bitSign (rows r i)*bitSign (rows r j))=0 := by
    have hh : (∑ r : Fin N,(1/(N : ℝ))*((bitSign (rows r i) : ℝ)*(bitSign (rows r j) : ℝ)))=0 := by
      calc
        _ = ∑ a : S,(1/(N : ℝ))*((bitSign (a.val i) : ℝ)*(bitSign (a.val j) : ℝ)) :=
          Equiv.sum_comp e.symm (fun a : S => (1/(N : ℝ))*((bitSign (a.val i) : ℝ)*(bitSign (a.val j) : ℝ)))
        _ = ∑ a : S,q a*((bitSign (a.val i) : ℝ)*(bitSign (a.val j) : ℝ)) := by simp only [huni]
        _ = ∑ a,q a*((bitSign (a i) : ℝ)*(bitSign (a j) : ℝ)) := activeSupport_sum q (fun a => (bitSign (a i) : ℝ)*(bitSign (a j) : ℝ))
        _ = 0 := by simpa only [mul_assoc] using hpair i j hij
    rw [← Finset.mul_sum] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left hn
    exact_mod_cast hz
  refine ⟨rows,sign_moments_strength_two rows hf hp,?_,?_⟩
  · intro a b h
    apply e.symm.injective
    apply Subtype.ext
    exact h
  · intro x
    constructor
    · intro hx
      refine ⟨e ⟨x,hx⟩,?_⟩
      simp [rows]
    · rintro ⟨r,rfl⟩
      exact (e.symm r).property

theorem indexed_support_intersection_card {N d : ℕ} (rows : Fin N → Fin d → Bool)
    (hinj : Function.Injective rows) (S T : Finset (Fin d → Bool))
    (hrange : ∀ x,x∈T ↔ ∃ r,rows r=x) :
    (S∩T).card=(Finset.univ.filter (fun r => rows r∈S)).card := by
  classical
  let K := Finset.univ.filter (fun r => rows r∈S)
  have himage : K.image rows=S∩T := by
    ext x
    constructor
    · intro hx
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hr).2,(hrange (rows r)).mpr ⟨r,rfl⟩⟩
    · intro hx
      obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
      obtain ⟨r,rfl⟩ := (hrange x).mp hxT
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ r,hxS⟩,rfl⟩
  rw [← himage,Finset.card_image_of_injective K hinj]

theorem minimal_support_code_rigidity {N r : ℕ} (hN : 12≤N) (hres : N%8=4)
    (C : Submodule (ZMod 2) (Fin (N-4) → ZMod 2)) (hC : Module.finrank (ZMod 2) C≤r)
    (S : Finset (Fin (N-4) → Bool)) (hS : S.card=N)
    (hSC : ∀ x∈S,binarySeed x∈C)
    (q : (Fin (N-4) → Bool) → ℝ) (hq : ∀ x,0≤q x) (hmass : ∑ x,q x=1)
    (hmean : ∀ i,∑ x,q x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)
    (hcard : (activeSupport q).card≤N) :
    (S∩activeSupport q).card≤r+4 ∧
      1-((r+4 : ℕ) : ℝ)/(N : ℝ)≤totalVariation (uniformFiniteLaw S) q ∧
      N-r-4≤(activeSupport q \ S).card ∧
      (activeSupport q).card=N ∧ ∀ x : activeSupport q,q x=1/(N : ℝ) := by
  classical
  obtain ⟨hT,huni⟩ := minimal_cube_target_uniform hN hres q hq hmass hmean hpair hcard
  obtain ⟨rows,hOA,hinj,hrange⟩ := minimal_cube_target_array hN hres q hq hmass hmean hpair hcard
  let T := activeSupport q
  let K := Finset.univ.filter (fun i : Fin N => rows i∈S)
  have hK : K⊆codeInsideRows (binaryObservationMatrix rows) C := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact hSC (rows i) (Finset.mem_filter.mp hi).2
  have hcount : (S∩T).card=K.card := indexed_support_intersection_card rows hinj S T hrange
  have hover : (S∩T).card≤r+4 := by
    rw [hcount]
    exact (Finset.card_le_card hK).trans (minimal_target_code_overlap hN hres rows hOA C hC)
  have hqEq : q=uniformFiniteLaw T := uniform_on_activeSupport q N hT huni
  have hTV : totalVariation (uniformFiniteLaw S) q=1-((S∩T).card : ℝ)/(N : ℝ) := by
    calc
      _ = totalVariation (uniformFiniteLaw S) (uniformFiniteLaw T) := congrArg (totalVariation (uniformFiniteLaw S)) hqEq
      _ = _ := uniformFiniteLaw_variation (by omega) S T hS hT
  have hNR : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hoverR : ((S∩T).card : ℝ)≤((r+4 : ℕ) : ℝ) := by exact_mod_cast hover
  have hdiv : ((S∩T).card : ℝ)/(N : ℝ)≤((r+4 : ℕ) : ℝ)/(N : ℝ) :=
    (div_le_div_iff_of_pos_right hNR).mpr hoverR
  refine ⟨hover,by rw [hTV]; linarith,?_,hT,huni⟩
  rw [Finset.card_sdiff,hT]
  change (S∩activeSupport q).card≤r+4 at hover
  omega
end EntropyDesigns
