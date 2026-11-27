/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage0
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage8 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (512+i.val)) → (512+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage9 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (576+i.val)) → (576+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage10 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (640+i.val)) → (640+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage11 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (704+i.val)) → (704+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage12 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (768+i.val)) → (768+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage13 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (832+i.val)) → (832+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage14 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (896+i.val)) → (896+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage15 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (960+i.val)) → (960+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
