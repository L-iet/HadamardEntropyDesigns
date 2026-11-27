/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
The two canonical parity spaces and normalization into their anchored forms. -/
module
public import EntropyQuadraticClassification.NormalizeAnchors
public import EntropyQuadraticClassification.SupportPacking
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

def planeBlocks : List (Finset (Fin 12) × Fin 12) :=
  [(encodedSupport 15,0),(encodedSupport 240,4),(encodedSupport 3840,8)]

def independentBlocks : List (Finset (Fin 12) × Fin 12) :=
  [(encodedSupport 255,0),(encodedSupport 3840,8)]

def blockChecks (blocks : List (Finset (Fin 12) × Fin 12)) : Finset (Finset (Fin 12)) :=
  (blocks.map Prod.fst).toFinset

def CanonicalFor (blocks : List (Finset (Fin 12) × Fin 12)) (s : Finset (Fin 12)) : Prop :=
  SatisfiesChecks (blockChecks blocks) s ∧ s.card%4=2 ∧ ∀ p∈blocks,p.2∉s

def satisfiesChecksDecidable (checks : Finset (Finset (Fin 12)))
    (s : Finset (Fin 12)) : Decidable (SatisfiesChecks checks s) := by
  unfold SatisfiesChecks
  exact Finset.decidableDforallFinset
attribute [instance] satisfiesChecksDecidable

def canonicalForDecidable (blocks : List (Finset (Fin 12) × Fin 12))
    (s : Finset (Fin 12)) : Decidable (CanonicalFor blocks s) := by
  letI : Decidable (∀ p∈blocks,p.2∉s) := List.decidableBAll (fun p => p.2∉s) blocks
  unfold CanonicalFor
  infer_instance
attribute [instance] canonicalForDecidable

theorem normalize_to_canonical (blocks : List (Finset (Fin 12) × Fin 12))
    (hu : ∀ p∈blocks,p.1.card%4=0 ∧
      SatisfiesChecks (blockChecks blocks) p.1 ∧ p.1∈blockChecks blocks)
    (ha : ∀ p∈blocks,p.2∈p.1)
    (hd : blocks.Pairwise (fun p q => Disjoint p.1 q.1))
    (s : Finset (Fin 12)) (hs : SatisfiesChecks (blockChecks blocks) s)
    (hq : s.card%4=2) : CanonicalFor blocks (normalizeBlocks blocks s) := by
  refine ⟨normalizeBlocks_checks blocks _ s hs (fun p hp => (hu p hp).2.1),?_,
    normalizeBlocks_anchors blocks s ha hd⟩
  rw [normalizeBlocks_card blocks _ s hs hu]
  exact hq

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeBlocks_valid :
    (∀ p∈planeBlocks,p.1.card%4=0 ∧
      SatisfiesChecks (blockChecks planeBlocks) p.1 ∧ p.1∈blockChecks planeBlocks) ∧
    (∀ p∈planeBlocks,p.2∈p.1) ∧
    planeBlocks.Pairwise (fun p q => Disjoint p.1 q.1) := by
  simp only [planeBlocks,List.forall_mem_cons,List.forall_mem_nil,and_true]
  decide +kernel

theorem independentBlocks_valid :
    (∀ p∈independentBlocks,p.1.card%4=0 ∧
      SatisfiesChecks (blockChecks independentBlocks) p.1 ∧ p.1∈blockChecks independentBlocks) ∧
    (∀ p∈independentBlocks,p.2∈p.1) ∧
    independentBlocks.Pairwise (fun p q => Disjoint p.1 q.1) := by
  simp only [independentBlocks,List.forall_mem_cons,List.forall_mem_nil,and_true]
  decide +kernel

end EntropyDesigns.QuadraticRefinement
