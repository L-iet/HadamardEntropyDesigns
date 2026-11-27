module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Finset.Range
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace HadamardMultibase
def HadamardOrder (n : ℕ) : Prop :=
  0 < n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

def IsBinary {n : ℕ} (A : Fin n → ℤ) : Prop := ∀ i, A i = 1 ∨ A i = -1

/-- Aperiodic autocorrelation, with no wraparound; shifts ≥ n have empty sums. -/
def autocorrelation {n : ℕ} (A : Fin n → ℤ) (s : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n - s),
    (if h : j + s < n then A ⟨j, by omega⟩ * A ⟨j + s, h⟩ else 0)

def IsGolayPair {n : ℕ} (A B : Fin n → ℤ) : Prop :=
  IsBinary A ∧ IsBinary B ∧
    ∀ s : ℕ, 0 < s → s < n → autocorrelation A s + autocorrelation B s = 0

def GolayLength (n : ℕ) : Prop :=
  0 < n ∧ ∃ A B : Fin n → ℤ, IsGolayPair A B

end HadamardMultibase
namespace EntropyDesigns
open HadamardMultibase
theorem finite_radix_hadamard_bound (k w : ℕ) (hk : 0<k)
    (hcert : ∀ a : ℕ,a<2^k → ∃ l : List ℕ,
      (∀ n∈l,GolayLength n) ∧ l.sum=a ∧ l.length≤w)
    {p : ℕ} (hp : Odd p) (hp1 : 1<p) :
    ∃ t : ℕ,HadamardOrder (2^t*p) ∧
      t≤2*w*Nat.clog (2^k) ((p-1)/2+1)+2 ∧
      (t:ℝ)≤(2*(w:ℝ)/(k:ℝ))*(Real.log (p:ℝ)/Real.log 2)+2*(w:ℝ)+2 := by sorry
end EntropyDesigns
