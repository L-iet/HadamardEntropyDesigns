/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage4
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage40 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2560+i.val)) → (2560+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage41 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2624+i.val)) → (2624+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage42 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2688+i.val)) → (2688+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage43 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2752+i.val)) → (2752+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage44 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2816+i.val)) → (2816+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage45 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2880+i.val)) → (2880+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage46 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2944+i.val)) → (2944+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage47 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3008+i.val)) → (3008+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
