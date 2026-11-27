/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Complete finite parity correspondence; actual verification is recorded separately. -/
module
public import EntropyQuadraticClassification.IndependentCacheBridge16
public import EntropyQuadraticClassification.IndependentCachedBranch245
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
theorem independent_cached_parity_bridge : ∀ x∈independentCanonicalVertices,
    ∀ y∈independentCanonicalVertices,independentCachedEdge x y ↔ encodedEdge x y := by
  have hc : ∀ x∈independentCanonicalVertices,x∈independentBridgeMembers0 ∨ x∈independentBridgeMembers1 ∨ x∈independentBridgeMembers2 ∨ x∈independentBridgeMembers3 ∨ x∈independentBridgeMembers4 ∨ x∈independentBridgeMembers5 ∨ x∈independentBridgeMembers6 ∨ x∈independentBridgeMembers7 ∨ x∈independentBridgeMembers8 ∨ x∈independentBridgeMembers9 ∨ x∈independentBridgeMembers10 ∨ x∈independentBridgeMembers11 ∨ x∈independentBridgeMembers12 ∨ x∈independentBridgeMembers13 ∨ x∈independentBridgeMembers14 ∨ x∈independentBridgeMembers15 ∨ x∈independentBridgeMembers16 := by decide +kernel
  intro x hx y hy
  rcases hc x hx with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16
  · exact independentBridgeParity0 x h0 y hy
  · exact independentBridgeParity1 x h1 y hy
  · exact independentBridgeParity2 x h2 y hy
  · exact independentBridgeParity3 x h3 y hy
  · exact independentBridgeParity4 x h4 y hy
  · exact independentBridgeParity5 x h5 y hy
  · exact independentBridgeParity6 x h6 y hy
  · exact independentBridgeParity7 x h7 y hy
  · exact independentBridgeParity8 x h8 y hy
  · exact independentBridgeParity9 x h9 y hy
  · exact independentBridgeParity10 x h10 y hy
  · exact independentBridgeParity11 x h11 y hy
  · exact independentBridgeParity12 x h12 y hy
  · exact independentBridgeParity13 x h13 y hy
  · exact independentBridgeParity14 x h14 y hy
  · exact independentBridgeParity15 x h15 y hy
  · exact independentBridgeParity16 x h16 y hy
theorem independent_canonical_clique_bound :
    ListCliqueBound encodedEdge independentCanonicalVertices 7 := by
  intro L hL hp
  have hpc : L.Pairwise independentCachedEdge := List.Pairwise.imp_of_mem
    (fun {x y} hx hy hxy =>
      (independent_cached_parity_bridge x (hL x hx) y (hL y hy)).mpr hxy) hp
  exact independentCachedBranchBound10654 L hL hpc
end EntropyDesigns.QuadraticRefinement
