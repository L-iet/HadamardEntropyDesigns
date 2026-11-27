/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Sharp actual quadratic-observable classification; verification is recorded separately. -/
module
public import EntropyQuadraticClassification.QuadraticPlaneSharp
public import EntropyQuadraticClassification.IndependentNormalizedBound
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

theorem independent_omitted_frame_sharp (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3) :
    HasQuadraticObservableFrame S 7 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤7 := by
  refine ⟨independent_omitted_seven_frame S hS hdim,?_⟩
  rcases quadratic_check_types_affine_dimension S hS with ⟨hd,h,hh,hh0,hs⟩|⟨hd,h⟩
  · intro m hframe
    exact quadratic_single_check_upper S hS h hh hh0 hs independent_block_parity_bound hframe
  · omega

theorem twelve_label_quadratic_classification (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    (Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=2 ∧
      HasQuadraticObservableFrame S 5 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤5) ∨
    (Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3 ∧
      HasQuadraticObservableFrame S 7 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤7) := by
  rcases quadratic_check_types_affine_dimension S hS with ⟨hd,h⟩|⟨hd,h⟩
  · exact Or.inr ⟨hd,independent_omitted_frame_sharp S hS hd⟩
  · exact Or.inl ⟨hd,plane_omitted_frame_sharp S hS hd⟩

theorem twelve_label_at_least_five (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    HasQuadraticObservableFrame S 5 := every_twelve_labels_five_frame S hS

theorem twelve_label_no_eight (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    ¬HasQuadraticObservableFrame S 8 := by
  intro hframe
  rcases twelve_label_quadratic_classification S hS with ⟨hd,hf,hb⟩|⟨hd,hf,hb⟩
  · have h := hb 8 hframe
    omega
  · have h := hb 8 hframe
    omega

end EntropyDesigns.QuadraticRefinement
