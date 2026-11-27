/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Every twelve-label quadratic restriction has exactly one of two check types. -/
module
public import EntropyQuadraticClassification.CheckGenerators
public import EntropyQuadraticClassification.QuadraticDualWeight
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement

theorem four_variable_quadratic_dimension :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode 4 2)=11 := by
  rw [lowDegreeBooleanCode_finrank]
  decide

theorem twelve_label_quadratic_dual_ne_bot
    (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))≠⊥ := by
  classical
  intro hz
  have hd := (binaryFunctionDotForm S).finrank_orthogonal
    (binaryFunctionDotForm_nondegenerate S)
    ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
  have hb := Submodule.finrank_map_le (binaryFunctionRestriction S) (lowDegreeBooleanCode 4 2)
  rw [four_variable_quadratic_dimension] at hb
  have ha : Module.finrank (ZMod 2) (S → ZMod 2)=12 := by simp [hS]
  rw [hz,ha] at hd
  simp only [finrank_bot] at hd
  omega

theorem twelve_label_quadratic_check_types
    (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    let D := (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
    ∃ h∈D,h≠0 ∧
      (D=Submodule.span (ZMod 2) {h} ∨
        ∃ g∈D,g≠0 ∧ h≠g ∧ D=Submodule.span (ZMod 2) {h,g}) := by
  classical
  dsimp only
  have hproper : S≠Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    rw [hS] at hc
    have hu : (Finset.univ : Finset (Finset (Fin 4))).card=16 := by decide
    rw [hu] at hc
    omega
  have hcard : Fintype.card S=12 := by simp [hS]
  have hw : ∀ f∈(binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)),
      f≠0 → (oneSupport f).card=8 := by
    intro f hf hzero
    exact quadratic_dual_weight_eight S hproper f hf hzero
  rcases constant_weight_generators hcard _ hw with hz|h
  · exact (twelve_label_quadratic_dual_ne_bot S hS hz).elim
  · exact h

end EntropyDesigns.QuadraticRefinement
