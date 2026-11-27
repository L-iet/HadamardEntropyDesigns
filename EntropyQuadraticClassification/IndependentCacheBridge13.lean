/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCacheBridge12
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentBridgeMembers13 : Finset ℕ := ([3130,3132,3150,3158,3162,3164,3174,3178] : List ℕ).toFinset
theorem independentBridgeParity13 : ∀ x∈independentBridgeMembers13,∀ y∈independentCanonicalVertices,
    independentCachedEdge x y ↔ encodedEdge x y := by decide +kernel
end EntropyDesigns.QuadraticRefinement
