/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete64word certificate blocks; acceptance requires a successful kernel check. -/
module
public import EntropyQuadraticClassification.IndependentCoverage3
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independentCanonicalCoverage32 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2048+i.val)) → (2048+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage33 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2112+i.val)) → (2112+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage34 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2176+i.val)) → (2176+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage35 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2240+i.val)) → (2240+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage36 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2304+i.val)) → (2304+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage37 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2368+i.val)) → (2368+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage38 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2432+i.val)) → (2432+i.val)∈independentCanonicalVertices := by decide +kernel
theorem independentCanonicalCoverage39 : ∀ i : Fin 64,
    CanonicalFor independentBlocks (encodedSupport (2496+i.val)) → (2496+i.val)∈independentCanonicalVertices := by decide +kernel
end EntropyDesigns.QuadraticRefinement
