/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Unconditional lower frames on every twelve-label set and sharpness in the affine-plane case. -/
module
public import EntropyQuadraticClassification.QuadraticFrameUpper
public import EntropyQuadraticClassification.CheckDimensions
public import EntropyQuadraticClassification.PlaneNormalizedBound
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

theorem quadratic_frame_mono (S : Finset (Finset (Fin 4))) {n m : ℕ}
    (hnm : n≤m) (hframe : HasQuadraticObservableFrame S m) : HasQuadraticObservableFrame S n := by
  obtain ⟨rows,hrows,F,hF,hm⟩ := hframe
  let e : Fin n → Fin m := Fin.castLE hnm
  refine ⟨(fun z i => rows z (e i)),?_,(fun i => F (e i)),(fun i => hF (e i)),?_⟩
  · constructor
    · intro i
      exact hrows.1 (e i)
    · intro i j hij
      apply hrows.2 (e i) (e j)
      intro he
      apply hij
      exact Fin.ext (congrArg (fun x : Fin m => x.val) he)
  · intro i z
    exact hm (e i) z

theorem every_twelve_labels_five_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    HasQuadraticObservableFrame S 5 := by
  obtain ⟨h,hh,hh0,hcase⟩ := twelve_label_quadratic_check_types S hS
  rcases hcase with hs|⟨g,hg,hg0,hhg,hp⟩
  · exact quadratic_frame_mono S (by decide : 5≤7) (quadratic_single_check_frame S hS h hh hh0 hs)
  · exact quadratic_two_check_frame S hS h g hh hg hh0 hg0 hhg hp

theorem independent_omitted_seven_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3) :
    HasQuadraticObservableFrame S 7 := by
  rcases quadratic_check_types_affine_dimension S hS with ⟨hd,h,hh,hh0,hs⟩|⟨hd,h⟩
  · exact quadratic_single_check_frame S hS h hh hh0 hs
  · omega

theorem plane_omitted_frame_sharp (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=2) :
    HasQuadraticObservableFrame S 5 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤5 := by
  refine ⟨every_twelve_labels_five_frame S hS,?_⟩
  rcases quadratic_check_types_affine_dimension S hS with ⟨hd,h⟩|⟨hd,h,hh,g,hg,hh0,hg0,hhg,hp⟩
  · omega
  · intro m hframe
    exact quadratic_two_check_upper S hS h g hh hg hh0 hg0 hhg hp plane_block_parity_bound hframe

end EntropyDesigns.QuadraticRefinement
