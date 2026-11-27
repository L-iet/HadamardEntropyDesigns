/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.CanonicalGraphTransfer
public import EntropyQuadraticClassification.IndependentCachedGraph
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage0 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (0+i.val)) → (0+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage1 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (64+i.val)) → (64+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage2 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (128+i.val)) → (128+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage3 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (192+i.val)) → (192+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage4 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (256+i.val)) → (256+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage5 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (320+i.val)) → (320+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage6 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (384+i.val)) → (384+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage7 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (448+i.val)) → (448+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
