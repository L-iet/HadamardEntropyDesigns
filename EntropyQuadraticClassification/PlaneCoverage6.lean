/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage5
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage48 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3072+i.val)) → (3072+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage49 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3136+i.val)) → (3136+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage50 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3200+i.val)) → (3200+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage51 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3264+i.val)) → (3264+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage52 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3328+i.val)) → (3328+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage53 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3392+i.val)) → (3392+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage54 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3456+i.val)) → (3456+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage55 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3520+i.val)) → (3520+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
