/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Twelve-bit words encode the same finite-set parity relation used above. -/
module
public import EntropyQuadraticClassification.Transvections
public import EntropyQuadraticClassification.CliqueCertificateRules
public import Mathlib.Data.Fintype.Powerset
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

def encodedSupport (word : ℕ) : Finset (Fin 12) :=
  Finset.univ.filter (fun j => word.testBit j.val=true)

def encodedEdge (x y : ℕ) : Prop := dotParity (encodedSupport x) (encodedSupport y)=1

def encodedEdgeDecidable (x y : ℕ) : Decidable (encodedEdge x y) :=
  inferInstanceAs (Decidable (dotParity (encodedSupport x) (encodedSupport y)=1))
attribute [instance] encodedEdgeDecidable

theorem encodedEdge_symm {x y : ℕ} : encodedEdge x y → encodedEdge y x := by
  unfold encodedEdge
  rw [dotParity_comm]
  exact id

end EntropyDesigns.QuadraticRefinement
