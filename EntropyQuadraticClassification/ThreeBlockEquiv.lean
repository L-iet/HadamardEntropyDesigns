/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Relabel two independent weight-eight checks into three canonical four-blocks. -/
module
public import EntropyQuadraticClassification.FiberTransport
public import EntropyQuadraticClassification.ParityPartitions
public import EntropyQuadraticClassification.EncodedParityGraph
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def threeClass (M N : Finset ι) (x : ι) : Fin 3 :=
  if x∈M then if x∈N then 2 else 0 else 1

def canonicalThreeClass (x : Fin 12) : Fin 3 := ⟨x.val/4,by omega⟩

theorem threeClass_fibers (M N : Finset ι) :
    Finset.univ.filter (fun x => threeClass M N x=0)=M \ N ∧
    Finset.univ.filter (fun x => threeClass M N x=1)=Finset.univ \ M ∧
    Finset.univ.filter (fun x => threeClass M N x=2)=M ∩ N := by
  refine ⟨?_,?_,?_⟩ <;> ext x
  all_goals
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,Finset.mem_inter]
    by_cases hm : x∈M <;> by_cases hn : x∈N <;> simp [threeClass,hm,hn]

theorem canonicalThreeClass_fibers :
    Finset.univ.filter (fun x => canonicalThreeClass x=0)=encodedSupport 15 ∧
    Finset.univ.filter (fun x => canonicalThreeClass x=1)=encodedSupport 240 ∧
    Finset.univ.filter (fun x => canonicalThreeClass x=2)=encodedSupport 3840 := by decide +kernel

theorem three_four_partition_equiv (hι : Fintype.card ι=12)
    (M N : Finset ι) (hM : M.card=8) (hN : N.card=8) (hX : (M ∆ N).card=8) :
    ∃ e : ι ≃ Fin 12,(M \ N).map e.toEmbedding=encodedSupport 15 ∧
      (Finset.univ \ M).map e.toEmbedding=encodedSupport 240 ∧
      (M ∩ N).map e.toEmbedding=encodedSupport 3840 := by
  classical
  have hcards := three_blocks_card M N hM hN hX
  have hcomp : (Finset.univ \ M).card=4 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset ι) M
    simp only [Finset.card_univ,Finset.univ_inter,hι,hM] at h
    omega
  have ht : (encodedSupport 15).card=4 ∧ (encodedSupport 240).card=4 ∧
      (encodedSupport 3840).card=4 := by decide +kernel
  have hs := threeClass_fibers M N
  have hf := canonicalThreeClass_fibers
  have hcard : ∀ j : Fin 3,Fintype.card {x : ι // threeClass M N x=j}=
      Fintype.card {y : Fin 12 // canonicalThreeClass y=j} := by
    intro j
    fin_cases j
    · calc
        _ = (Finset.univ.filter (fun x => threeClass M N x=0)).card := Fintype.card_subtype _
        _ = (M \ N).card := congrArg Finset.card hs.1
        _ = 4 := hcards.1
        _ = (encodedSupport 15).card := ht.1.symm
        _ = (Finset.univ.filter (fun x => canonicalThreeClass x=0)).card := (congrArg Finset.card hf.1).symm
        _ = _ := (Fintype.card_subtype _).symm
    · calc
        _ = (Finset.univ.filter (fun x => threeClass M N x=1)).card := Fintype.card_subtype _
        _ = (Finset.univ \ M).card := congrArg Finset.card hs.2.1
        _ = 4 := hcomp
        _ = (encodedSupport 240).card := ht.2.1.symm
        _ = (Finset.univ.filter (fun x => canonicalThreeClass x=1)).card := (congrArg Finset.card hf.2.1).symm
        _ = _ := (Fintype.card_subtype _).symm
    · calc
        _ = (Finset.univ.filter (fun x => threeClass M N x=2)).card := Fintype.card_subtype _
        _ = (M ∩ N).card := congrArg Finset.card hs.2.2
        _ = 4 := hcards.2.2
        _ = (encodedSupport 3840).card := ht.2.2.symm
        _ = (Finset.univ.filter (fun x => canonicalThreeClass x=2)).card := (congrArg Finset.card hf.2.2).symm
        _ = _ := (Fintype.card_subtype _).symm
  obtain ⟨e,he⟩ := exists_fiber_respecting_equiv (threeClass M N) canonicalThreeClass hcard
  refine ⟨e,?_,?_,?_⟩
  · have h := support_map_fiber e (threeClass M N) canonicalThreeClass he 0
    simpa only [hs.1,hf.1] using h
  · have h := support_map_fiber e (threeClass M N) canonicalThreeClass he 1
    simpa only [hs.2.1,hf.2.1] using h
  · have h := support_map_fiber e (threeClass M N) canonicalThreeClass he 2
    simpa only [hs.2.2,hf.2.2] using h

end EntropyDesigns.QuadraticRefinement
