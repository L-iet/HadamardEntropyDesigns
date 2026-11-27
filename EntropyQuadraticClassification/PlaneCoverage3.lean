/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage2
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage24 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1536+i.val)) → (1536+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage25 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1600+i.val)) → (1600+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage26 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1664+i.val)) → (1664+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage27 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1728+i.val)) → (1728+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage28 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1792+i.val)) → (1792+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage29 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1856+i.val)) → (1856+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage30 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1920+i.val)) → (1920+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage31 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1984+i.val)) → (1984+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
