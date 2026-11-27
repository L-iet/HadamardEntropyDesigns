/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage5
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage48 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3072+i.val)) → (3072+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage49 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3136+i.val)) → (3136+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage50 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3200+i.val)) → (3200+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage51 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3264+i.val)) → (3264+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage52 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3328+i.val)) → (3328+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage53 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3392+i.val)) → (3392+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage54 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3456+i.val)) → (3456+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage55 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3520+i.val)) → (3520+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
