/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.CanonicalGraphTransfer
public import EntropyQuadraticClassification.PlaneBranch6
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage0 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (0+i.val)) → (0+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage1 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (64+i.val)) → (64+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage2 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (128+i.val)) → (128+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage3 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (192+i.val)) → (192+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage4 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (256+i.val)) → (256+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage5 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (320+i.val)) → (320+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage6 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (384+i.val)) → (384+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage7 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (448+i.val)) → (448+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
