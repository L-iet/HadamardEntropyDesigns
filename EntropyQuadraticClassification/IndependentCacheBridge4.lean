/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCacheBridge3
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentBridgeMembers4 : Finset ℕ := ([1594,1596,1614,1622,1626,1628,1638,1642] : List ℕ).toFinset
theorem independentBridgeParity4 : ∀ x∈independentBridgeMembers4,∀ y∈independentCanonicalVertices,
    independentCachedEdge x y ↔ encodedEdge x y := by decide +kernel
end EntropyDesigns.QuadraticRefinement
