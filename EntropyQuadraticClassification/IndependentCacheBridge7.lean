/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCacheBridge6
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentBridgeMembers7 : Finset ℕ := ([1740,1746,1748,1752,1762,1764,1768,1776] : List ℕ).toFinset
theorem independentBridgeParity7 : ∀ x∈independentBridgeMembers7,∀ y∈independentCanonicalVertices,
    independentCachedEdge x y ↔ encodedEdge x y := by decide +kernel
end EntropyDesigns.QuadraticRefinement
