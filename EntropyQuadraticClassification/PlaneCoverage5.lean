/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.PlaneCoverage4
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem planeCanonicalCoverage40 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2560+i.val)) → (2560+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage41 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2624+i.val)) → (2624+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage42 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2688+i.val)) → (2688+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage43 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2752+i.val)) → (2752+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage44 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2816+i.val)) → (2816+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage45 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2880+i.val)) → (2880+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage46 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (2944+i.val)) → (2944+i.val)∈planeBranchMembers218 := by decide +kernel
theorem planeCanonicalCoverage47 : ∀ i : Fin 64,
    CanonicalFor planeBlocks (encodedSupport (3008+i.val)) → (3008+i.val)∈planeBranchMembers218 := by decide +kernel
end EntropyDesigns.QuadraticRefinement
