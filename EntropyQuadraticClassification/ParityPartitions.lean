/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Finite-set partitions forced by two weight-eight binary checks. -/
module
public import EntropyQuadraticClassification.BlockNormalization
public import Mathlib.Data.Fintype.Card
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weight_eight_intersection (M N : Finset ι)
    (hM : M.card=8) (hN : N.card=8) (hX : (M ∆ N).card=8) :
    (M ∩ N).card=4 := by
  have h := symmetric_difference_weight M N
  omega

theorem weight_eight_union (M N : Finset ι)
    (hM : M.card=8) (hN : N.card=8) (hX : (M ∆ N).card=8) :
    (M ∪ N).card=12 := by
  have hi := weight_eight_intersection M N hM hN hX
  have hu := Finset.card_union_add_card_inter M N
  omega

theorem weight_eight_covers (hι : Fintype.card ι=12) (M N : Finset ι)
    (hM : M.card=8) (hN : N.card=8) (hX : (M ∆ N).card=8) :
    M ∪ N=Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ,hι,weight_eight_union M N hM hN hX]

theorem covered_intersection_xor (M N : Finset ι) (h : M ∪ N=Finset.univ) :
    M ∩ N=Finset.univ ∆ (M ∆ N) := by
  ext x
  have hx : x∈M ∨ x∈N := by
    have hx' : x∈M ∪ N := by rw [h]; exact Finset.mem_univ x
    exact Finset.mem_union.mp hx'
  simp only [Finset.mem_inter,Finset.mem_symmDiff,Finset.mem_univ]
  tauto

theorem sdiff_as_intersection_xor (M N : Finset ι) :
    M \ N=M ∆ (M ∩ N) := by
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_symmDiff,Finset.mem_inter]
  tauto

theorem dotParity_univ (s : Finset ι) : dotParity s Finset.univ=s.card%2 := by
  simp [dotParity]

theorem complement_even_check (s M : Finset ι)
    (hs : s.card%2=0) (hM : dotParity s M=0) :
    dotParity s (Finset.univ \ M)=0 := by
  have he : Finset.univ \ M=Finset.univ ∆ M := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_symmDiff,Finset.mem_univ]
    tauto
  rw [he,dotParity_xor_right,dotParity_univ,hs,hM]

theorem three_blocks_even (s M N : Finset ι)
    (hcover : M ∪ N=Finset.univ) (hs : s.card%2=0)
    (hM : dotParity s M=0) (hN : dotParity s N=0) :
    dotParity s (M \ N)=0 ∧ dotParity s (N \ M)=0 ∧
      dotParity s (M ∩ N)=0 := by
  have hi : dotParity s (M ∩ N)=0 := by
    rw [covered_intersection_xor M N hcover,dotParity_xor_right,
      dotParity_xor_right,dotParity_univ,hs,hM,hN]
  have ha : dotParity s (M \ N)=0 := by
    rw [sdiff_as_intersection_xor,dotParity_xor_right,hM,hi]
  have hb : dotParity s (N \ M)=0 := by
    rw [sdiff_as_intersection_xor,Finset.inter_comm N M,
      dotParity_xor_right,hN,hi]
  exact ⟨ha,hb,hi⟩

theorem three_blocks_card (M N : Finset ι)
    (hM : M.card=8) (hN : N.card=8) (hX : (M ∆ N).card=8) :
    (M \ N).card=4 ∧ (N \ M).card=4 ∧ (M ∩ N).card=4 := by
  have hi := weight_eight_intersection M N hM hN hX
  have ha := Finset.card_sdiff_add_card_inter M N
  have hb := Finset.card_sdiff_add_card_inter N M
  rw [Finset.inter_comm N M] at hb
  omega

end EntropyDesigns.QuadraticRefinement
