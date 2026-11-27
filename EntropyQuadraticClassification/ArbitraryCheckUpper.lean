/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Transport canonical parity-clique estimates to arbitrary weight-eight checks. -/
module
public import EntropyQuadraticClassification.TwoBlockEquiv
public import EntropyQuadraticClassification.ThreeBlockEquiv
public import EntropyQuadraticClassification.CanonicalBlocks
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
open scoped symmDiff

def CanonicalCliqueEstimate (blocks : List (Finset (Fin 12) × Fin 12)) (b : ℕ) : Prop :=
  ∀ L : List (Finset (Fin 12)),
    (∀ s∈L,SatisfiesChecks (blockChecks blocks) s ∧ s.card%4=2) →
    L.Pairwise (fun s t => dotParity s t=1) → L.length≤b

theorem blockChecks_iff (blocks : List (Finset (Fin 12) × Fin 12)) (s : Finset (Fin 12)) :
    SatisfiesChecks (blockChecks blocks) s ↔ ∀ p∈blocks,dotParity s p.1=0 := by
  constructor
  · intro h p hp
    apply h p.1
    change p.1∈(blocks.map Prod.fst).toFinset
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · intro h M hM
    change M∈(blocks.map Prod.fst).toFinset at hM
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hM)
    exact h p hp

theorem single_check_clique_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι=12) (M : Finset ι) (hM : M.card=8)
    (hcanonical : CanonicalCliqueEstimate independentBlocks 7)
    (L : List (Finset ι))
    (hL : ∀ s∈L,s.card%4=2 ∧ dotParity s M=0)
    (hp : L.Pairwise (fun s t => dotParity s t=1)) : L.length≤7 := by
  classical
  obtain ⟨e,heM,heComp⟩ := eight_four_partition_equiv hι M hM
  let f : Finset ι → Finset (Fin 12) := fun s => s.map e.toEmbedding
  have hmem : ∀ t∈L.map f,SatisfiesChecks (blockChecks independentBlocks) t ∧ t.card%4=2 := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    have hq := (hL s hs).1
    have hsM := (hL s hs).2
    have hseven : s.card%2=0 := by omega
    have hsComp := complement_even_check s M hseven hsM
    constructor
    · apply (blockChecks_iff _ _).mpr
      intro p hpm
      simp only [independentBlocks,List.mem_cons,List.mem_nil_iff,or_false] at hpm
      rcases hpm with rfl|rfl
      · change dotParity (s.map e.toEmbedding) (encodedSupport 255)=0
        rw [←heM,support_map_dot]
        exact hsM
      · change dotParity (s.map e.toEmbedding) (encodedSupport 3840)=0
        rw [←heComp,support_map_dot]
        exact hsComp
    · simpa only [f,Finset.card_map] using hq
  have hpair : (L.map f).Pairwise (fun s t => dotParity s t=1) :=
    List.pairwise_map.mpr (hp.imp (fun {s t} hst => (support_map_dot e s t).trans hst))
  simpa only [List.length_map] using hcanonical (L.map f) hmem hpair

theorem two_check_clique_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι=12) (M N : Finset ι)
    (hM : M.card=8) (hN : N.card=8) (hX : (M ∆ N).card=8)
    (hcanonical : CanonicalCliqueEstimate planeBlocks 5)
    (L : List (Finset ι))
    (hL : ∀ s∈L,s.card%4=2 ∧ dotParity s M=0 ∧ dotParity s N=0)
    (hp : L.Pairwise (fun s t => dotParity s t=1)) : L.length≤5 := by
  classical
  obtain ⟨e,heA,heComp,heC⟩ := three_four_partition_equiv hι M N hM hN hX
  have hcover := weight_eight_covers hι M N hM hN hX
  let f : Finset ι → Finset (Fin 12) := fun s => s.map e.toEmbedding
  have hmem : ∀ t∈L.map f,SatisfiesChecks (blockChecks planeBlocks) t ∧ t.card%4=2 := by
    intro t ht
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
    obtain ⟨hq,hsM,hsN⟩ := hL s hs
    have hseven : s.card%2=0 := by omega
    have hblocks := three_blocks_even s M N hcover hseven hsM hsN
    have hsComp := complement_even_check s M hseven hsM
    constructor
    · apply (blockChecks_iff _ _).mpr
      intro p hpm
      simp only [planeBlocks,List.mem_cons,List.mem_nil_iff,or_false] at hpm
      rcases hpm with rfl|rfl|rfl
      · change dotParity (s.map e.toEmbedding) (encodedSupport 15)=0
        rw [←heA,support_map_dot]
        exact hblocks.1
      · change dotParity (s.map e.toEmbedding) (encodedSupport 240)=0
        rw [←heComp,support_map_dot]
        exact hsComp
      · change dotParity (s.map e.toEmbedding) (encodedSupport 3840)=0
        rw [←heC,support_map_dot]
        exact hblocks.2.2
    · simpa only [f,Finset.card_map] using hq
  have hpair : (L.map f).Pairwise (fun s t => dotParity s t=1) :=
    List.pairwise_map.mpr (hp.imp (fun {s t} hst => (support_map_dot e s t).trans hst))
  simpa only [List.length_map] using hcanonical (L.map f) hmem hpair

end EntropyDesigns.QuadraticRefinement
