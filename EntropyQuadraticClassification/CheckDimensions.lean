/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Relate the two check-space types to the affine dimension of the omitted labels. -/
module
public import EntropyQuadraticClassification.QuadraticCheckTypes
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace EntropyDesigns.QuadraticRefinement
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem binary_pair_linearIndependent {h g : ι → ZMod 2}
    (hh : h≠0) (hg : g≠0) (hhg : h≠g) : LinearIndependent (ZMod 2) ![h,g] := by
  apply LinearIndependent.pair_iff.mpr
  intro s t he
  rcases gf2_two_cases s with rfl|rfl <;> rcases gf2_two_cases t with rfl|rfl
  · exact ⟨rfl,rfl⟩
  · have hz : g=0 := by simpa using he
    exact (hg hz).elim
  · have hz : h=0 := by simpa using he
    exact (hh hz).elim
  · have hz : h+g=0 := by simpa using he
    exact (hhg ((binary_add_eq_zero_iff h g).mp hz)).elim

theorem binary_pair_span_finrank {h g : ι → ZMod 2}
    (hh : h≠0) (hg : g≠0) (hhg : h≠g) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {h,g})=2 := by
  have hlin := binary_pair_linearIndependent hh hg hhg
  have hrange : Set.range ![h,g]=({h,g} : Set (ι → ZMod 2)) := by
    ext f
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hf
      rcases hf with rfl|hf
      · exact ⟨0,rfl⟩
      · have he : f=g := hf
        subst f
        exact ⟨1,rfl⟩
  have hd := finrank_span_eq_card hlin
  rw [hrange] at hd
  simpa using hd

theorem binary_singleton_span_finrank {h : ι → ZMod 2} (hh : h≠0) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {h})=1 :=
  finrank_span_singleton hh

theorem twelve_quadratic_dual_dimension (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    Module.finrank (ZMod 2) ((binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))=
        4-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S)) := by
  classical
  have hproper : S≠Finset.univ := by
    intro he
    have hc := congrArg Finset.card he
    have hu : (Finset.univ : Finset (Finset (Fin 4))).card=16 := by decide
    rw [hS,hu] at hc
    omega
  have hc := degree_sub_two_restriction_dimension (by decide : 2≤4) S hproper
  change Module.finrank (ZMod 2) ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))=
    S.card-(4-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))) at hc
  rw [hS] at hc
  have hd := (binaryFunctionDotForm S).finrank_orthogonal
    (binaryFunctionDotForm_nondegenerate S)
    ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
  have ha : Module.finrank (ZMod 2) (S → ZMod 2)=12 := by simp [hS]
  rw [ha] at hd
  omega

theorem quadratic_check_types_affine_dimension
    (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    let D := (binaryFunctionDotForm S).orthogonal
      ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S))
    (Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3 ∧
      ∃ h∈D,h≠0 ∧ D=Submodule.span (ZMod 2) {h}) ∨
    (Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=2 ∧
      ∃ h∈D,∃ g∈D,h≠0 ∧ g≠0 ∧ h≠g ∧ D=Submodule.span (ZMod 2) {h,g}) := by
  classical
  dsimp only
  obtain ⟨h,hh,hh0,hcase⟩ := twelve_label_quadratic_check_types S hS
  have hd := twelve_quadratic_dual_dimension S hS
  rcases hcase with hs|⟨g,hg,hg0,hhg,hp⟩
  · left
    have hr : Module.finrank (ZMod 2) ((binaryFunctionDotForm S).orthogonal
        ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))=1 := by
      rw [hs]
      exact binary_singleton_span_finrank hh0
    exact ⟨by omega,h,hh,hh0,hs⟩
  · right
    have hr : Module.finrank (ZMod 2) ((binaryFunctionDotForm S).orthogonal
        ((lowDegreeBooleanCode 4 2).map (binaryFunctionRestriction S)))=2 := by
      rw [hp]
      exact binary_pair_span_finrank hh0 hg0 hhg
    exact ⟨by omega,h,hh,g,hg,hh0,hg0,hhg,hp⟩

end EntropyDesigns.QuadraticRefinement
