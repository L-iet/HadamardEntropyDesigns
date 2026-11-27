module
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Card
@[expose] public section
namespace EntropyDesigns
def IsBinaryStrengthTwo {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop :=
  ∀ i j,i≠j → ∀ a b : Bool,
    4*(Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)).card=N

def ternaryPaleyOrder (e : ℕ) : ℕ :=
  if e%2=0 then 2*(3^e+1) else 3^e+1

theorem explicit_cofinite_central_ray (d : ℕ) (hd : 2≤d) :
    ∃ k e A B : ℕ,
      A=2^k ∧ 0<e ∧ 4*B=ternaryPaleyOrder e ∧
      d+1≤4*A ∧ (∀ j<k,4*2^j<d+1) ∧
      d+1≤4*B ∧ (∀ j<e,0<j → ternaryPaleyOrder j<d+1) ∧
      4*(A-1)*(B-1)<3*(d+1)^2 ∧
      ∀ N : ℕ,0<N → 4∣N → 4*(A-1)*(B-1)≤N →
        ∃ rows : Fin N → Fin d → Bool,IsBinaryStrengthTwo rows := by sorry
end EntropyDesigns
