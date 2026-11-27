/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Check unequal colors before evaluating adjacency in a finite certificate. -/
module
public import EntropyQuadraticClassification.CliqueCertificateRules
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {V : Type*} [DecidableEq V]

theorem cliqueBound_coloring_separated {R : V → V → Prop} (S : Finset V)
    (b : ℕ) (color : V → ℕ) (hc : ∀ x∈S,color x<b)
    (hproper : ∀ x∈S,∀ y∈S,color x≠color y ∨ ¬R x y) :
    ListCliqueBound R S b := by
  apply cliqueBound_coloring S b color hc
  intro x hx y hy hxy
  rcases hproper x hx y hy with h|h
  · exact h
  · exact (h hxy).elim

end EntropyDesigns.QuadraticRefinement
