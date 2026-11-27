/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.ZMod.Basic
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
noncomputable section
open scoped BigOperators ComplexOrder Matrix
def tensorVector {A : Type*} (k : ℕ) (v : A → ℂ) (x : Fin k → A) : ℂ :=
  ∏ i, v (x i)

def pureTensor {A : Type*} (k : ℕ) (v : A → ℂ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  Matrix.vecMulVec (tensorVector k v) (star (tensorVector k v))

def traceFirst {A : Type*} [Fintype A] {k : ℕ}
    (M : Matrix (Fin (k+1) → A) (Fin (k+1) → A) ℂ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  fun x y => ∑ a, M (Fin.cons a x) (Fin.cons a y)

def uniformHierarchy {S A : Type*} [Fintype S] (v : S → A → ℂ) (k : ℕ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  (1/(Fintype.card S : ℝ)) • ∑ z, pureTensor k (v z)


def randomSign {A : Type*} (ε : A → Bool) (i : A) : ℝ := if ε i then -1 else 1


def signedShift {G : Type*} [AddGroup G] [DecidableEq G]
    (t : G) (ε : G → Bool) : Matrix G G ℝ :=
  fun i j => if j=i+t then randomSign ε i else 0


def shiftVector {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) (a : G×G) : ℂ :=
  ((signedShift t ε a.1 a.2 / Real.sqrt (Fintype.card G:ℝ) : ℝ):ℂ)


def shiftEnsemble {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] :
    (G × (G → Bool)) → (G×G) → ℂ := fun z => shiftVector z.1 z.2


def shiftHierarchy {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (k : ℕ) :
    Matrix (Fin k → G×G) (Fin k → G×G) ℂ :=
  uniformHierarchy (shiftEnsemble (G:=G)) k

/-- A concrete finite probability ensemble of real orthogonals with pure
maximally entangled conditional factors, every level of an actual complex
density hierarchy, consistency, symmetry, uniform one-copy average, and
no flat factor. All levels use the same displayed ensemble. -/
def FullShiftHierarchy (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nontrivial G] : Prop :=
  (0<1/(Fintype.card (G × (G → Bool)):ℝ) ∧
    (∑ z : G × (G → Bool),1/(Fintype.card (G × (G → Bool)):ℝ))=1) ∧
  (∀ t : G,∀ ε : G → Bool,
    signedShift t ε ∈ Matrix.orthogonalGroup G ℝ ∧
    (∃ i j : G,signedShift t ε i j=0) ∧
    ¬∀ i j : G,(signedShift t ε i j)^2=1/(Fintype.card G:ℝ)) ∧
  (∀ t : G,∀ ε : G → Bool,
    (∑ a : G×G,shiftVector t ε a*star (shiftVector t ε a))=1 ∧
    (pureTensor 1 (shiftVector t ε)).PosSemidef ∧
    Matrix.trace (pureTensor 1 (shiftVector t ε))=1 ∧
    ∀ i a : G,(∑ j,shiftVector t ε (i,j)*star (shiftVector t ε (a,j)))=
      ((if i=a then 1/(Fintype.card G:ℝ) else 0:ℝ):ℂ)) ∧
  (∀ k : ℕ,(shiftHierarchy (G:=G) k).PosSemidef ∧ Matrix.trace (shiftHierarchy (G:=G) k)=1) ∧
  (∀ k : ℕ,∀ π : Equiv.Perm (Fin k),∀ x y : Fin k → G×G,
    shiftHierarchy k (x ∘ π) (y ∘ π)=shiftHierarchy k x y) ∧
  (∀ k : ℕ,traceFirst (shiftHierarchy (G:=G) (k+1))=shiftHierarchy k) ∧
  (∀ a b : G×G,shiftHierarchy 1 (fun _ => a) (fun _ => b)=
    ((if a=b then 1/(Fintype.card G:ℝ)^2 else 0:ℝ):ℂ))


theorem pureTensor_posSemidef {A : Type*} [Fintype A] (k : ℕ) (v : A → ℂ) :
    (pureTensor k v).PosSemidef := by sorry

theorem pureTensor_trace {A : Type*} [Fintype A] (k : ℕ) (v : A → ℂ)
    (hv : ∑ a,v a*star (v a)=1) : Matrix.trace (pureTensor k v)=1 := by sorry

theorem pureTensor_consistent {A : Type*} [Fintype A] (k : ℕ) (v : A → ℂ)
    (hv : ∑ a,v a*star (v a)=1) :
    traceFirst (pureTensor (k+1) v)=pureTensor k v := by sorry

theorem uniformHierarchy_posSemidef {S A : Type*} [Fintype S] [Fintype A]
    (v : S → A → ℂ) (k : ℕ) : (uniformHierarchy v k).PosSemidef := by sorry

theorem uniformHierarchy_reindex {S A : Type*} [Fintype S] (v : S → A → ℂ)
    (k : ℕ) (π : Equiv.Perm (Fin k)) (x y : Fin k → A) :
    uniformHierarchy v k (x ∘ π) (y ∘ π)=uniformHierarchy v k x y := by sorry

theorem uniformHierarchy_trace {S A : Type*} [Fintype S] [Nonempty S] [Fintype A]
    (v : S → A → ℂ) (hv : ∀ z, ∑ a,v z a*star (v z a)=1) (k : ℕ) :
    Matrix.trace (uniformHierarchy v k)=1 := by sorry

theorem uniformHierarchy_consistent {S A : Type*} [Fintype S] [Fintype A]
    (v : S → A → ℂ) (hv : ∀ z, ∑ a,v z a*star (v z a)=1) (k : ℕ) :
    traceFirst (uniformHierarchy v (k+1))=uniformHierarchy v k := by sorry

theorem randomSign_sum {A : Type*} [Fintype A] [DecidableEq A] (i : A) :
    (∑ ε : A → Bool,randomSign ε i)=0 := by sorry

theorem randomSign_pair_sum {A : Type*} [Fintype A] [DecidableEq A] (i j : A) :
    (∑ ε : A → Bool,randomSign ε i*randomSign ε j)=
      if i=j then (Fintype.card (A → Bool):ℝ) else 0 := by sorry

theorem signedShift_orthogonal {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) : signedShift t ε ∈ Matrix.orthogonalGroup G ℝ := by sorry

theorem signedShift_has_zero {G : Type*} [AddGroup G] [Nontrivial G] [DecidableEq G]
    (t : G) (ε : G → Bool) : ∃ i j : G,signedShift t ε i j=0 := by sorry

theorem signedShift_not_flat {G : Type*} [AddGroup G] [Fintype G] [Nontrivial G] [DecidableEq G]
    (t : G) (ε : G → Bool) :
    ¬∀ i j : G,(signedShift t ε i j)^2=1/(Fintype.card G:ℝ) := by sorry

theorem shiftVector_normalized {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) : (∑ a : G×G,shiftVector t ε a*star (shiftVector t ε a))=1 := by sorry

theorem shiftVector_reduced_state {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (t : G) (ε : G → Bool) (i a : G) :
    (∑ j,shiftVector t ε (i,j)*star (shiftVector t ε (a,j)))=
      ((if i=a then 1/(Fintype.card G:ℝ) else 0:ℝ):ℂ) := by sorry

theorem shiftEnsemble_one_copy {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (a b : G×G) :
    uniformHierarchy (shiftEnsemble (G:=G)) 1 (fun _ => a) (fun _ => b)=
      ((if a=b then 1/(Fintype.card G:ℝ)^2 else 0:ℝ):ℂ) := by sorry

theorem full_shift_hierarchy {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Nontrivial G] :
    FullShiftHierarchy G := by sorry

theorem every_dimension_false_positive (n : ℕ) (hn : 1<n) :
    ∃ (G : Type) (hG : AddCommGroup G) (hF : Fintype G)
      (hD : DecidableEq G) (hN : Nontrivial G),
      @Fintype.card G hF=n ∧ @FullShiftHierarchy G hG hF hD hN := by sorry

end
end EntropyDesigns.ExchangeableHierarchy
