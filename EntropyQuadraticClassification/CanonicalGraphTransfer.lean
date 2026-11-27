/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Transport a finite encoded graph bound to arbitrary checked block-parity supports. -/
module
public import EntropyQuadraticClassification.CanonicalBlocks
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

theorem block_parity_clique_bound (blocks : List (Finset (Fin 12) × Fin 12))
    (hu : ∀ p∈blocks,p.1.card%4=0 ∧
      SatisfiesChecks (blockChecks blocks) p.1 ∧ p.1∈blockChecks blocks)
    (ha : ∀ p∈blocks,p.2∈p.1)
    (hd : blocks.Pairwise (fun p q => Disjoint p.1 q.1))
    (vertices : Finset ℕ) (b : ℕ)
    (hcover : ∀ s,CanonicalFor blocks s → packedSupport s∈vertices)
    (hbound : ListCliqueBound encodedEdge vertices b)
    (L : List (Finset (Fin 12)))
    (hL : ∀ s∈L,SatisfiesChecks (blockChecks blocks) s ∧ s.card%4=2)
    (hp : L.Pairwise (fun s t => dotParity s t=1)) : L.length≤b := by
  let f : Finset (Fin 12) → ℕ := fun s => packedSupport (normalizeBlocks blocks s)
  have hmem : ∀ w∈L.map f,w∈vertices := by
    intro w hw
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hw
    exact hcover _ (normalize_to_canonical blocks hu ha hd s (hL s hs).1 (hL s hs).2)
  have hrel : ∀ {s t},s∈L → t∈L → dotParity s t=1 → encodedEdge (f s) (f t) := by
    intro s t hs ht hst
    change dotParity (encodedSupport (packedSupport (normalizeBlocks blocks s)))
      (encodedSupport (packedSupport (normalizeBlocks blocks t)))=1
    rw [encodedSupport_packedSupport,encodedSupport_packedSupport,
      normalizeBlocks_dot blocks _ s t (hL s hs).1 (hL t ht).1 hu]
    exact hst
  have hpair : (L.map f).Pairwise encodedEdge :=
    List.pairwise_map.mpr (List.Pairwise.imp_of_mem hrel hp)
  simpa only [List.length_map] using hbound (L.map f) hmem hpair

end EntropyDesigns.QuadraticRefinement
