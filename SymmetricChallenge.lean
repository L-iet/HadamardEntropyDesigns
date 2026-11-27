/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
namespace EntropyDesigns
noncomputable section
def bitSign (b : Bool) : ℤ := if b then -1 else 1
def shannon {α : Type*} [Fintype α] (w : α → ℝ) : ℝ := -(∑ a,w a*Real.log (w a))
namespace SymmetricEntropy
def CoordinatePermutationInvariant {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin d),∀ x : Fin d → Bool,w (fun i => x (σ i))=w x
theorem symmetric_pairwise_shannon_lower {d : ℕ} (hd : 2≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    ((d:ℝ)-1)*Real.log 2-Real.log ((d:ℝ)+1)≤shannon w := by sorry
end SymmetricEntropy
end
end EntropyDesigns
