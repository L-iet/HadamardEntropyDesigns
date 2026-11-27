/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage6
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage56 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3584+i.val)) → (3584+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage57 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3648+i.val)) → (3648+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage58 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3712+i.val)) → (3712+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage59 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3776+i.val)) → (3776+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage60 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3840+i.val)) → (3840+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage61 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3904+i.val)) → (3904+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage62 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3968+i.val)) → (3968+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage63 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (4032+i.val)) → (4032+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
