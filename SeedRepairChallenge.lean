/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Basis
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
@[expose] public section
namespace EntropyDesigns
noncomputable section

def squarefreeBooleanMonomial {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) : ZMod 2 := if s ⊆ z then 1 else 0

def lowDegreeBooleanCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun s : {s : Finset (Fin r) // s.card≤d} =>
    squarefreeBooleanMonomial s.val))

def booleanValueSign (a : ZMod 2) : ℤ := if a=0 then 1 else -1

def booleanSupportVector {r : ℕ} (z : Finset (Fin r)) : Fin r → ZMod 2 :=
  fun i => if i∈z then 1 else 0

def binaryFunctionRestriction {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (ι → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2) where
  toFun f := fun z => f z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



def IsBinaryStrengthTwo {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop :=
  ∀ i j,i≠j → ∀ a b : Bool,
    4*(Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)).card=N

def binaryObservationMatrix {N d : ℕ} (rows : Fin N → Fin d → Bool) :
    Matrix (Fin N) (Fin d) (ZMod 2) := fun r i => if rows r i then 1 else 0



def HasDegreeHadamardSeedEncoding {d : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (r D : ℕ) : Prop :=
  ∃ labels : Fin (d+1) → Finset (Fin r),Function.Injective labels ∧
    ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r D) ∧
      (∀ j i,booleanValueSign (f i (labels j))=H j i.succ)






open scoped BigOperators

def binaryFunctionDotForm (ι : Type*) [Fintype ι] :
    LinearMap.BilinForm (ZMod 2) (ι → ZMod 2) := dotProductBilin (ZMod 2) (ZMod 2)


def omittedBooleanVectors {r : ℕ} (S : Finset (Finset (Fin r))) : Set (Fin r → ZMod 2) :=
  booleanSupportVector '' (Sᶜ : Set (Finset (Fin r)))


def binaryParityLinear (ι : Type*) [Fintype ι] : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ i,f i
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

def evenBinaryCode {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  C ⊓ LinearMap.ker (binaryParityLinear ι)


def binaryCodeRadical {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  C ⊓ (binaryFunctionDotForm ι).orthogonal C

def binaryBilinearRank {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) : ℕ :=
  Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range
    (fun x : C => fun y : C => ∑ i,x.val i*y.val i)))




def bitSign (b : Bool) : ℤ := if b then -1 else 1

def IsUniformBinaryPairwiseIndependent {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : Prop :=
  (∀ i,(∑ z,bitSign (rows z i))=0) ∧
    (∀ i j,i≠j → (∑ z,bitSign (rows z i)*bitSign (rows z j))=0)




namespace SupportRepair
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

def uniformSupportTruthLaw {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (rows : α → δ) (v : δ) : ℝ :=
  ∑ z∈S,if rows z=v then 1/(S.card : ℝ) else 0

section
variable {α : Type*} [DecidableEq α]
def OneSupportExchange (S T : Finset α) : Prop :=
  ∃ a∈S,∃ b∉S,T=insert b (S.erase a)

def SupportExchangePath : ℕ → Finset α → Finset α → Prop
  | 0,S,T => S=T
  | n+1,S,T => ∃ U,OneSupportExchange S U ∧ SupportExchangePath n U T

end

section
variable {α δ : Type*} [Fintype α] [DecidableEq α] [DecidableEq δ]
def TruthExchangePathWith (P : Finset α → (α → δ) → Prop) :
    ℕ → Finset α → (α → δ) → Finset α → (α → δ) → Prop
  | 0,T,rows,U,finalRows => T=U ∧ rows=finalRows ∧ P T rows
  | n+1,T,rows,U,finalRows => P T rows ∧
      ∃ a∈T,∃ b∉T,TruthExchangePathWith P n (insert b (T.erase a))
        (fun z => rows (Equiv.swap a b z)) U finalRows

end

def labelAffineCodimension {r : ℕ} (T : Finset (Finset (Fin r))) : ℕ :=
  r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (booleanSupportVector '' (T : Set (Finset (Fin r)))))

def HasTruthDegree {r d : ℕ} (D : ℕ) (T : Finset (Finset (Fin r)))
    (rows : Finset (Fin r) → Fin d → Bool) : Prop :=
  ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
    (∀ i,f i∈lowDegreeBooleanCode r D) ∧
    (∀ i z,z∉T → f i z=if rows z i then 1 else 0)

theorem minimum_support_exchanges {r d : ℕ} (hr : 2≤r)
    (T : Finset (Finset (Fin r))) (hcard : r+1≤T.card)
    (rows : Finset (Fin r) → Fin d → Bool) :
    ∃ (U : Finset (Finset (Fin r))) (finalRows : Finset (Fin r) → Fin d → Bool),
      U.card=T.card ∧
      affineSpan (ZMod 2) (booleanSupportVector '' (U : Set (Finset (Fin r))))=⊤ ∧
      TruthExchangePathWith
        (fun V nr => HasTruthDegree (r-1) V nr ∧
          uniformSupportTruthLaw (Vᶜ) nr=uniformSupportTruthLaw (Tᶜ) rows)
        (labelAffineCodimension T) T rows U finalRows ∧
      HasTruthDegree (r-2) U finalRows ∧
      uniformSupportTruthLaw (Uᶜ) finalRows=uniformSupportTruthLaw (Tᶜ) rows ∧
      (∀ k W,SupportExchangePath k T W →
        affineSpan (ZMod 2) (booleanSupportVector '' (W : Set (Finset (Fin r))))=⊤ →
          labelAffineCodimension T≤k) := by
  sorry

theorem boolean_support_exchange_lower {r k : ℕ} (T U : Finset (Finset (Fin r)))
    (hcard : r+1≤T.card) (hpath : SupportExchangePath k T U)
    (hspan : affineSpan (ZMod 2) (booleanSupportVector '' (U : Set (Finset (Fin r))))=⊤) :
    labelAffineCodimension T≤k := by
  sorry

theorem one_exchange_truth_law_preserved {α δ : Type*} [DecidableEq α] [DecidableEq δ]
    (S : Finset α) (a b : α) (ha : a∉S) (hb : b∈S) (rows : α → δ) :
    uniformSupportTruthLaw (insert a (S.erase b)) (fun z => rows (Equiv.swap a b z))=
      uniformSupportTruthLaw S rows := by
  sorry

end SupportRepair
end
end EntropyDesigns
