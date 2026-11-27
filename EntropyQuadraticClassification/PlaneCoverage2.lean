/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage1
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage16 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1024+i.val)) → (1024+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage17 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1088+i.val)) → (1088+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage18 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1152+i.val)) → (1152+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage19 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1216+i.val)) → (1216+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage20 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1280+i.val)) → (1280+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage21 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1344+i.val)) → (1344+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage22 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1408+i.val)) → (1408+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage23 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (1472+i.val)) → (1472+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
