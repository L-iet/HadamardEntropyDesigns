/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
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




open scoped BigOperators

def signCorrelation {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) (i j : Fin m) : ℤ :=
  ∑ z,(bitSign (rows z i)*bitSign (rows z j))

def correlatedPairs {ι : Type*} [Fintype ι] {m : ℕ} (rows : ι → Fin m → Bool) :
    Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter fun ij => ij.1 < ij.2 ∧ signCorrelation rows ij.1 ij.2≠0

def augmentedObservable {ι : Type*} {m : ℕ} (rows : ι → Fin m → Bool)
    (z : ι) : Fin (m+1) → ℤ := Fin.cons 1 (fun i => bitSign (rows z i))

def momentEntryError {ι : Type*} [Fintype ι] {m : ℕ} (rows : ι → Fin m → Bool)
    (i j : Fin (m+1)) : ℝ :=
  (((∑ z,((augmentedObservable rows z i : ℝ)*(augmentedObservable rows z j : ℝ)))/
    (Fintype.card ι : ℝ))-(if i=j then 1 else 0))^2

def augmentedMomentError {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : ℝ :=
  ∑ ij : Fin (m+1) × Fin (m+1),momentEntryError rows ij.1 ij.2

theorem punctured_moment_error_floor {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hres : S.card%8=4) (hproper : S≠Finset.univ)
    (rows : S → Fin (S.card-4) → Bool) (hmean : ∀ i,(∑ z,bitSign (rows z i))=0)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    let a := r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))
    2*a-3≤(correlatedPairs rows).card ∧
      32*((2*a-3 : ℕ) : ℝ)/(S.card : ℝ)^2≤augmentedMomentError rows := by
  sorry

theorem four_omitted_moment_error_floor {r : ℕ} (hr : 5≤r)
    (S : Finset (Finset (Fin r))) (horder : S.card=2^r-4)
    (rows : S → Fin (S.card-4) → Bool) (hmean : ∀ i,(∑ z,bitSign (rows z i))=0)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    2*r-9≤(correlatedPairs rows).card ∧
      32*((2*r-9 : ℕ) : ℝ)/(S.card : ℝ)^2≤augmentedMomentError rows := by
  sorry

end
end EntropyDesigns
