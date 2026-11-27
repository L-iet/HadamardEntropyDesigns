/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage0
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage8 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (512+i.val)) → (512+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage9 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (576+i.val)) → (576+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage10 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (640+i.val)) → (640+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage11 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (704+i.val)) → (704+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage12 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (768+i.val)) → (768+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage13 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (832+i.val)) → (832+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage14 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (896+i.val)) → (896+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage15 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (960+i.val)) → (960+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
