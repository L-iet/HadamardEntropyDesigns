/- Copyright (c) 2026 Joshua Mark. Apache-2.0.
Independent concrete specification of quadratic sign observables on twelve labels. -/
module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Combination
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators
noncomputable section

def bitSign (b : Bool) : ℤ := if b then -1 else 1

def squarefreeBooleanMonomial {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) : ZMod 2 := if s ⊆ z then 1 else 0

def lowDegreeBooleanCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun s : {s : Finset (Fin r) // s.card≤d} =>
    squarefreeBooleanMonomial s.val))

def booleanSupportVector {r : ℕ} (z : Finset (Fin r)) : Fin r → ZMod 2 :=
  fun i => if i∈z then 1 else 0

def omittedBooleanVectors {r : ℕ} (S : Finset (Finset (Fin r))) : Set (Fin r → ZMod 2) :=
  booleanSupportVector '' (Sᶜ : Set (Finset (Fin r)))

def IsUniformBinaryPairwiseIndependent {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : Prop :=
  (∀ i,(∑ z,bitSign (rows z i))=0) ∧
    (∀ i j,i≠j → (∑ z,bitSign (rows z i)*bitSign (rows z j))=0)

namespace QuadraticRefinement

def HasQuadraticObservableFrame (S : Finset (Finset (Fin 4))) (m : ℕ) : Prop :=
  ∃ rows : S → Fin m → Bool,IsUniformBinaryPairwiseIndependent rows ∧
    ∃ F : Fin m → (Finset (Fin 4) → ZMod 2),
      (∀ i,F i∈lowDegreeBooleanCode 4 2) ∧
      ∀ i (z : S),F i z.val=if rows z i then 1 else 0

theorem every_twelve_labels_five_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    HasQuadraticObservableFrame S 5 := by sorry

theorem independent_omitted_seven_frame (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3) :
    HasQuadraticObservableFrame S 7 := by sorry

theorem plane_omitted_frame_sharp (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=2) :
    HasQuadraticObservableFrame S 5 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤5 := by sorry

theorem independent_omitted_frame_sharp (S : Finset (Finset (Fin 4))) (hS : S.card=12)
    (hdim : Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3) :
    HasQuadraticObservableFrame S 7 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤7 := by sorry

theorem twelve_label_quadratic_classification (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    (Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=2 ∧
      HasQuadraticObservableFrame S 5 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤5) ∨
    (Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))=3 ∧
      HasQuadraticObservableFrame S 7 ∧ ∀ m,HasQuadraticObservableFrame S m → m≤7) := by sorry

theorem twelve_label_at_least_five (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    HasQuadraticObservableFrame S 5 := by sorry

theorem twelve_label_no_eight (S : Finset (Finset (Fin 4))) (hS : S.card=12) :
    ¬HasQuadraticObservableFrame S 8 := by sorry

end QuadraticRefinement
end
end EntropyDesigns
