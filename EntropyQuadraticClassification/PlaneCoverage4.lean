/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage3
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage32 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2048+i.val)) → (2048+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage33 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2112+i.val)) → (2112+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage34 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2176+i.val)) → (2176+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage35 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2240+i.val)) → (2240+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage36 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2304+i.val)) → (2304+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage37 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2368+i.val)) → (2368+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage38 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2432+i.val)) → (2432+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage39 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2496+i.val)) → (2496+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
