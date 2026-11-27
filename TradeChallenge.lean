module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Card
@[expose] public section
namespace EntropyDesigns
def bitSign (b : Bool) : ℤ := if b then -1 else 1

noncomputable def signObservation {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℝ) (c₀ r : ι) : {c : ι // c≠c₀} → Bool :=
  fun c => decide (H r c.val= -1)

def IsReducedObservationTrade {n : ℕ}
    (H K : Matrix (Fin n) (Fin n) ℝ) (c₀ : Fin n) (I : Finset (Fin n)) : Prop :=
  (∀ r,K r c₀=1) ∧
  Function.Injective (signObservation H c₀) ∧
  Function.Injective (signObservation K c₀) ∧
  (∀ r,r∉I → signObservation K c₀ r=signObservation H c₀ r) ∧
  (∀ r,r∈I → ∀ s,signObservation K c₀ r≠signObservation H c₀ s) ∧
  (∀ c : {c : Fin n // c≠c₀},
    (∑ r,(bitSign (signObservation K c₀ r c):ℝ))=
      ∑ r,(bitSign (signObservation H c₀ r c):ℝ)) ∧
  (∀ c d : {c : Fin n // c≠c₀},
    (∑ r,(bitSign (signObservation K c₀ r c):ℝ)*(bitSign (signObservation K c₀ r d):ℝ))=
      ∑ r,(bitSign (signObservation H c₀ r c):ℝ)*(bitSign (signObservation H c₀ r d):ℝ))

theorem universal_half_row_observation_trade {n : ℕ} (hn : 4<n)
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : Matrix.IsHadamard H)
    (c₀ : Fin n) (hzero : ∀ r,H r c₀=1) :
    ∃ I : Finset (Fin n),∃ K : Matrix (Fin n) (Fin n) ℝ,
      Matrix.IsHadamard K ∧ I.card=n/2 ∧ IsReducedObservationTrade H K c₀ I ∧
      ∀ c d : {c : Fin n // c≠c₀},∀ a b : Bool,
        (Finset.univ.filter (fun r => signObservation K c₀ r c=a ∧ signObservation K c₀ r d=b)).card=
        (Finset.univ.filter (fun r => signObservation H c₀ r c=a ∧ signObservation H c₀ r d=b)).card := by sorry
end EntropyDesigns
