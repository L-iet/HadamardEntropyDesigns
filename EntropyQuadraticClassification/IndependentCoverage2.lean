/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage1
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage16 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1024+i.val)) → (1024+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage17 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1088+i.val)) → (1088+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage18 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1152+i.val)) → (1152+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage19 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1216+i.val)) → (1216+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage20 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1280+i.val)) → (1280+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage21 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1344+i.val)) → (1344+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage22 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1408+i.val)) → (1408+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage23 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (1472+i.val)) → (1472+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
