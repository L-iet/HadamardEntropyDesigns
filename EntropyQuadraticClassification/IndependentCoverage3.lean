/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage2
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage24 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1536+i.val)) → (1536+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage25 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1600+i.val)) → (1600+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage26 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1664+i.val)) → (1664+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage27 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1728+i.val)) → (1728+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage28 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1792+i.val)) → (1792+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage29 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1856+i.val)) → (1856+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage30 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1920+i.val)) → (1920+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage31 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1984+i.val)) → (1984+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
