/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage6
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage56 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3584+i.val)) → (3584+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage57 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3648+i.val)) → (3648+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage58 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3712+i.val)) → (3712+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage59 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3776+i.val)) → (3776+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage60 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3840+i.val)) → (3840+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage61 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3904+i.val)) → (3904+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage62 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (3968+i.val)) → (3968+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage63 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (4032+i.val)) → (4032+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
