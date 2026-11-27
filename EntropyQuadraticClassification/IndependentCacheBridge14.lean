/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCacheBridge13
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentBridgeMembers14 : Finset ℕ := ([3180,3186,3188,3192,3214,3222,3226,3228] : List ℕ).toFinset
theorem independentBridgeParity14 : ∀ x∈independentBridgeMembers14,∀ y∈independentCanonicalVertices,
    independentCachedEdge x y ↔ encodedEdge x y := by decide +kernel
end EntropyDesigns.QuadraticRefinement
