/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Relabel any eight-plus-four partition into the canonical coordinate blocks. -/
module
public import EntropyQuadraticClassification.FiberTransport
public import EntropyQuadraticClassification.EncodedParityGraph
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def twoClass (M : Finset ι) (x : ι) : Fin 2 := if x∈M then 0 else 1

theorem twoClass_zero_fiber (M : Finset ι) :
    Finset.univ.filter (fun x => twoClass M x=0)=M := by
  ext x
  by_cases hx : x∈M <;> simp [twoClass,hx]

theorem twoClass_one_fiber (M : Finset ι) :
    Finset.univ.filter (fun x => twoClass M x=1)=Finset.univ \ M := by
  ext x
  by_cases hx : x∈M <;> simp [twoClass,hx]

theorem twoClass_zero_card (M : Finset ι) :
    Fintype.card {x // twoClass M x=0}=M.card := by
  rw [Fintype.card_subtype]
  exact congrArg Finset.card (twoClass_zero_fiber M)

theorem twoClass_one_card (M : Finset ι) :
    Fintype.card {x // twoClass M x=1}=(Finset.univ \ M).card := by
  rw [Fintype.card_subtype]
  exact congrArg Finset.card (twoClass_one_fiber M)

theorem eight_four_partition_equiv (hι : Fintype.card ι=12)
    (M : Finset ι) (hM : M.card=8) :
    ∃ e : ι ≃ Fin 12,M.map e.toEmbedding=encodedSupport 255 ∧
      (Finset.univ \ M).map e.toEmbedding=encodedSupport 3840 := by
  classical
  have hcomp : (Finset.univ \ M).card=4 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset ι) M
    simp only [Finset.card_univ,Finset.univ_inter,hι,hM] at h
    omega
  have hz : (encodedSupport 255).card=8 := by decide +kernel
  have ho : (Finset.univ \ encodedSupport 255)=encodedSupport 3840 := by decide +kernel
  have hoc : (encodedSupport 3840).card=4 := by decide +kernel
  have hcard : ∀ j : Fin 2,Fintype.card {x : ι // twoClass M x=j}=
      Fintype.card {y : Fin 12 // twoClass (encodedSupport 255) y=j} := by
    intro j
    fin_cases j
    · exact (twoClass_zero_card M).trans
        (hM.trans (hz.symm.trans (twoClass_zero_card (encodedSupport 255)).symm))
    · have ht : (Finset.univ \ encodedSupport 255).card=4 := by rw [ho,hoc]
      exact (twoClass_one_card M).trans
        (hcomp.trans (ht.symm.trans (twoClass_one_card (encodedSupport 255)).symm))
  obtain ⟨e,he⟩ := exists_fiber_respecting_equiv (twoClass M)
    (twoClass (encodedSupport 255)) hcard
  refine ⟨e,?_,?_⟩
  · have h := support_map_fiber e (twoClass M) (twoClass (encodedSupport 255)) he 0
    simpa only [twoClass_zero_fiber] using h
  · have h := support_map_fiber e (twoClass M) (twoClass (encodedSupport 255)) he 1
    simpa only [twoClass_one_fiber,ho] using h

end EntropyDesigns.QuadraticRefinement
