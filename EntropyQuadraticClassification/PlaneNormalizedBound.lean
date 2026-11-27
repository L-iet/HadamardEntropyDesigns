/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete support coverage and normalization transport; verification is recorded separately. -/
module
public import EntropyQuadraticClassification.PlaneCoverage7
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem plane_canonical_coverage (s : Finset (Fin 12)) (hs : CanonicalFor planeBlocks s) :
    packedSupport s∈planeBranchMembers218 := by
  let w := packedSupport s
  have hw : w<4096 := packedSupport_lt s
  let k : Fin 64 := ⟨w/64,by omega⟩
  let i : Fin 64 := ⟨w%64,Nat.mod_lt _ (by decide)⟩
  have he : w=64*k.val+i.val := by dsimp [k,i]; omega
  have hall : ∀ k : Fin 64,∀ i : Fin 64,
      CanonicalFor planeBlocks (encodedSupport (64*k.val+i.val)) → (64*k.val+i.val)∈planeBranchMembers218 := by
    intro k
    fin_cases k
    · exact planeCanonicalCoverage0
    · exact planeCanonicalCoverage1
    · exact planeCanonicalCoverage2
    · exact planeCanonicalCoverage3
    · exact planeCanonicalCoverage4
    · exact planeCanonicalCoverage5
    · exact planeCanonicalCoverage6
    · exact planeCanonicalCoverage7
    · exact planeCanonicalCoverage8
    · exact planeCanonicalCoverage9
    · exact planeCanonicalCoverage10
    · exact planeCanonicalCoverage11
    · exact planeCanonicalCoverage12
    · exact planeCanonicalCoverage13
    · exact planeCanonicalCoverage14
    · exact planeCanonicalCoverage15
    · exact planeCanonicalCoverage16
    · exact planeCanonicalCoverage17
    · exact planeCanonicalCoverage18
    · exact planeCanonicalCoverage19
    · exact planeCanonicalCoverage20
    · exact planeCanonicalCoverage21
    · exact planeCanonicalCoverage22
    · exact planeCanonicalCoverage23
    · exact planeCanonicalCoverage24
    · exact planeCanonicalCoverage25
    · exact planeCanonicalCoverage26
    · exact planeCanonicalCoverage27
    · exact planeCanonicalCoverage28
    · exact planeCanonicalCoverage29
    · exact planeCanonicalCoverage30
    · exact planeCanonicalCoverage31
    · exact planeCanonicalCoverage32
    · exact planeCanonicalCoverage33
    · exact planeCanonicalCoverage34
    · exact planeCanonicalCoverage35
    · exact planeCanonicalCoverage36
    · exact planeCanonicalCoverage37
    · exact planeCanonicalCoverage38
    · exact planeCanonicalCoverage39
    · exact planeCanonicalCoverage40
    · exact planeCanonicalCoverage41
    · exact planeCanonicalCoverage42
    · exact planeCanonicalCoverage43
    · exact planeCanonicalCoverage44
    · exact planeCanonicalCoverage45
    · exact planeCanonicalCoverage46
    · exact planeCanonicalCoverage47
    · exact planeCanonicalCoverage48
    · exact planeCanonicalCoverage49
    · exact planeCanonicalCoverage50
    · exact planeCanonicalCoverage51
    · exact planeCanonicalCoverage52
    · exact planeCanonicalCoverage53
    · exact planeCanonicalCoverage54
    · exact planeCanonicalCoverage55
    · exact planeCanonicalCoverage56
    · exact planeCanonicalCoverage57
    · exact planeCanonicalCoverage58
    · exact planeCanonicalCoverage59
    · exact planeCanonicalCoverage60
    · exact planeCanonicalCoverage61
    · exact planeCanonicalCoverage62
    · exact planeCanonicalCoverage63
  have hc : CanonicalFor planeBlocks (encodedSupport (64*k.val+i.val)) := by
    rw [←he]
    change CanonicalFor planeBlocks (encodedSupport (packedSupport s))
    rw [encodedSupport_packedSupport]
    exact hs
  change w∈planeBranchMembers218
  rw [he]
  exact hall k i hc
theorem plane_block_parity_bound (L : List (Finset (Fin 12)))
    (hL : ∀ s∈L,SatisfiesChecks (blockChecks planeBlocks) s ∧ s.card%4=2)
    (hp : L.Pairwise (fun s t => dotParity s t=1)) : L.length≤5 := by
  exact block_parity_clique_bound planeBlocks planeBlocks_valid.1
    planeBlocks_valid.2.1 planeBlocks_valid.2.2 planeBranchMembers218 5
    plane_canonical_coverage planeBranchBound218 L hL hp
end EntropyDesigns.QuadraticRefinement
