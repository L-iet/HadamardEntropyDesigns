/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCacheBridge15
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentBridgeMembers16 : Finset ℕ := ([3276,3282,3284,3288,3298,3300,3304,3312] : List ℕ).toFinset
theorem independentBridgeParity16 : ∀ x∈independentBridgeMembers16,∀ y∈independentCanonicalVertices,
    independentCachedEdge x y ↔ encodedEdge x y := by decide +kernel
end EntropyDesigns.QuadraticRefinement
