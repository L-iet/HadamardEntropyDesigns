/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCachedGraph
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
def independentBridgeMembers0 : Finset ℕ := ([6,10,12,18,20,24,34,36] : List ℕ).toFinset
theorem independentBridgeParity0 : ∀ x∈independentBridgeMembers0,∀ y∈independentCanonicalVertices,
    independentCachedEdge x y ↔ encodedEdge x y := by decide
end EntropyDesigns.QuadraticRefinement
