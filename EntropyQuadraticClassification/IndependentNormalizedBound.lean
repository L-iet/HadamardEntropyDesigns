/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete support coverage and normalization transport; verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCoverage7
public import EntropyQuadraticClassification.IndependentCanonicalBound
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independent_canonical_coverage (s : Finset (Fin 12)) (hs : CanonicalFor independentBlocks s) :
    packedSupport s∈independentCanonicalVertices := by
  let w := packedSupport s
  have hw : w<4096 := packedSupport_lt s
  let k : Fin 64 := ⟨w/64,by omega⟩
  let i : Fin 64 := ⟨w%64,Nat.mod_lt _ (by decide)⟩
  have he : w=64*k.val+i.val := by dsimp [k,i]; omega
  have hall : ∀ k : Fin 64,∀ i : Fin 64,
      CanonicalFor independentBlocks (encodedSupport (64*k.val+i.val)) → (64*k.val+i.val)∈independentCanonicalVertices := by
    intro k
    fin_cases k
    · exact independentCanonicalCoverage0
    · exact independentCanonicalCoverage1
    · exact independentCanonicalCoverage2
    · exact independentCanonicalCoverage3
    · exact independentCanonicalCoverage4
    · exact independentCanonicalCoverage5
    · exact independentCanonicalCoverage6
    · exact independentCanonicalCoverage7
    · exact independentCanonicalCoverage8
    · exact independentCanonicalCoverage9
    · exact independentCanonicalCoverage10
    · exact independentCanonicalCoverage11
    · exact independentCanonicalCoverage12
    · exact independentCanonicalCoverage13
    · exact independentCanonicalCoverage14
    · exact independentCanonicalCoverage15
    · exact independentCanonicalCoverage16
    · exact independentCanonicalCoverage17
    · exact independentCanonicalCoverage18
    · exact independentCanonicalCoverage19
    · exact independentCanonicalCoverage20
    · exact independentCanonicalCoverage21
    · exact independentCanonicalCoverage22
    · exact independentCanonicalCoverage23
    · exact independentCanonicalCoverage24
    · exact independentCanonicalCoverage25
    · exact independentCanonicalCoverage26
    · exact independentCanonicalCoverage27
    · exact independentCanonicalCoverage28
    · exact independentCanonicalCoverage29
    · exact independentCanonicalCoverage30
    · exact independentCanonicalCoverage31
    · exact independentCanonicalCoverage32
    · exact independentCanonicalCoverage33
    · exact independentCanonicalCoverage34
    · exact independentCanonicalCoverage35
    · exact independentCanonicalCoverage36
    · exact independentCanonicalCoverage37
    · exact independentCanonicalCoverage38
    · exact independentCanonicalCoverage39
    · exact independentCanonicalCoverage40
    · exact independentCanonicalCoverage41
    · exact independentCanonicalCoverage42
    · exact independentCanonicalCoverage43
    · exact independentCanonicalCoverage44
    · exact independentCanonicalCoverage45
    · exact independentCanonicalCoverage46
    · exact independentCanonicalCoverage47
    · exact independentCanonicalCoverage48
    · exact independentCanonicalCoverage49
    · exact independentCanonicalCoverage50
    · exact independentCanonicalCoverage51
    · exact independentCanonicalCoverage52
    · exact independentCanonicalCoverage53
    · exact independentCanonicalCoverage54
    · exact independentCanonicalCoverage55
    · exact independentCanonicalCoverage56
    · exact independentCanonicalCoverage57
    · exact independentCanonicalCoverage58
    · exact independentCanonicalCoverage59
    · exact independentCanonicalCoverage60
    · exact independentCanonicalCoverage61
    · exact independentCanonicalCoverage62
    · exact independentCanonicalCoverage63
  have hc : CanonicalFor independentBlocks (encodedSupport (64*k.val+i.val)) := by
    rw [←he]
    change CanonicalFor independentBlocks (encodedSupport (packedSupport s))
    rw [encodedSupport_packedSupport]
    exact hs
  change w∈independentCanonicalVertices
  rw [he]
  exact hall k i hc
theorem independent_block_parity_bound (L : List (Finset (Fin 12)))
    (hL : ∀ s∈L,SatisfiesChecks (blockChecks independentBlocks) s ∧ s.card%4=2)
    (hp : L.Pairwise (fun s t => dotParity s t=1)) : L.length≤7 := by
  exact block_parity_clique_bound independentBlocks independentBlocks_valid.1
    independentBlocks_valid.2.1 independentBlocks_valid.2.2 independentCanonicalVertices 7
    independent_canonical_coverage independent_canonical_clique_bound L hL hp
end EntropyDesigns.QuadraticRefinement
