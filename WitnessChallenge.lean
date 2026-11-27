/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Powerset
@[expose] public section
namespace EntropyDesigns
open scoped BigOperators
noncomputable section

def bitSign (b : Bool) : ℤ := if b then -1 else 1

noncomputable def uniformFiniteLaw {α : Type*} [DecidableEq α] (S : Finset α) (x : α) : ℝ :=
  if x∈S then 1/(S.card : ℝ) else 0

noncomputable def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1/2 : ℝ)*(∑ x,|p x-q x|)

namespace SupportWitness
variable {α : Type*} [Fintype α] [DecidableEq α]
def IsClique (R : α → α → Prop) (T : Finset α) : Prop :=
  ∀ a∈T,∀ b∈T,a≠b → R a b

def orthogonalityNumber (R : α → α → Prop) (S : Finset α) : ℕ := by
  classical
  exact S.powerset.sup fun T => if IsClique R T then T.card else 0

def blockLaws (R : α → α → Prop) (n : ℕ) : Set (α → ℝ) :=
  {q | ∃ T : Finset α,T.card=n ∧ IsClique R T ∧ q=uniformFiniteLaw T}

def augmentedOrthogonal {d : ℕ} (a b : Fin d → Bool) : Prop :=
  1+(∑ i,bitSign (a i)*bitSign (b i))=0

def hadamardMixtures (d : ℕ) : Set ((Fin d → Bool) → ℝ) :=
  convexHull ℝ (blockLaws (augmentedOrthogonal (d:=d)) (d+1))

theorem hadamard_mixture_support_witness {d : ℕ}
    (S : Finset (Fin d → Bool)) (p : (Fin d → Bool) → ℝ)
    (hp : ∑ x,p x=1) (hsupport : ∀ x,x∉S → p x=0)
    (q : (Fin d → Bool) → ℝ) (hq : q∈hadamardMixtures d) :
    1-(orthogonalityNumber augmentedOrthogonal S : ℝ)/(d+1 : ℕ)≤
      totalVariation p q := by
  sorry

theorem hadamard_block_replacement_bound {d b : ℕ}
    (S : Finset (Fin d → Bool)) (x y : Fin b → Fin (d+1) → (Fin d → Bool))
    (hx : ∀ j i,x j i∈S)
    (horth : ∀ j i k,i≠k → augmentedOrthogonal (y j i) (y j k)) :
    ((b*(d+1) : ℕ) : ℝ)*
      (1-(orthogonalityNumber augmentedOrthogonal S : ℝ)/(d+1 : ℕ))≤
      ∑ j,((Finset.univ.filter fun i => x j i≠y j i).card : ℝ) := by
  sorry

def augmentedSignMatrix {d : ℕ} (y : Fin (d+1) → (Fin d → Bool)) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℤ := fun i => Fin.cons 1 (fun j => bitSign (y i j))

theorem augmentedSignMatrix_isHadamard {d : ℕ} (y : Fin (d+1) → (Fin d → Bool))
    (horth : ∀ i j,i≠j → augmentedOrthogonal (y i) (y j)) :
    Matrix.IsHadamard (augmentedSignMatrix y) := by
  sorry

end SupportWitness
end
end EntropyDesigns
