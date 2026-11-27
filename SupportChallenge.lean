/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
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

theorem fixedSupport_degree_sub_two_extension_iff {r : ℕ} (hr : 2≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) :
    (∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-2), binaryFunctionRestriction S g=f) ↔
    affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin r) // z∉S} =>
      booleanSupportVector z.val))=⊤ := by sorry

theorem fixed_support_hadamard_degree_criterion {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (hproper : Finset.univ.image labels≠Finset.univ) :
    (∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r (r-2)) ∧
      (∀ j i,booleanValueSign (f i (labels j))=H j i.succ)) ↔
    affineSpan (ZMod 2) (Set.range
      (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} =>
        booleanSupportVector z.val))=⊤ := by sorry

def IsBinaryStrengthTwo {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop :=
  ∀ i j,i≠j → ∀ a b : Bool,
    4*(Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)).card=N

def binaryObservationMatrix {N d : ℕ} (rows : Fin N → Fin d → Bool) :
    Matrix (Fin N) (Fin d) (ZMod 2) := fun r i => if rows r i then 1 else 0


theorem fixed_support_pairwise_observables_criterion {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1)
    (labels : Fin (d+1) → Finset (Fin r)) (hinj : Function.Injective labels)
    (hproper : Finset.univ.image labels≠Finset.univ) :
    (∃ rows : Fin (d+1) → Fin d → Bool, IsBinaryStrengthTwo rows ∧
      ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
        (∀ i,f i∈lowDegreeBooleanCode r (r-2)) ∧
        (∀ i j,f i (labels j)=binaryObservationMatrix rows j i)) ↔
    affineSpan (ZMod 2) (Set.range
      (fun z : {z : Finset (Fin r) // z∉Finset.univ.image labels} =>
        booleanSupportVector z.val))=⊤ := by sorry

def HasDegreeHadamardSeedEncoding {d : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (r D : ℕ) : Prop :=
  ∃ labels : Fin (d+1) → Finset (Fin r),Function.Injective labels ∧
    ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
      (∀ i,f i∈lowDegreeBooleanCode r D) ∧
      (∀ j i,booleanValueSign (f i (labels j))=H j i.succ)


theorem degree_sub_two_encoding_iff_complement_capacity {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4) (hhi : d+1<2^r)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) :
    HasDegreeHadamardSeedEncoding H r (r-2) ↔ r+1≤2^r-(d+1) := by sorry

theorem minimal_seed_degree_saturation {d r : ℕ}
    (hN : 4≤d+1) (hr : 4≤r) (hres : (d+1)%8=4)
    (hlo : 2^(r-1)<d+1) (hhi : d+1<2^r)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) :
    (HasDegreeHadamardSeedEncoding H r (r-2) ↔ r+1≤2^r-(d+1)) ∧
    (2^r-(d+1)≤r → HasDegreeHadamardSeedEncoding H r (r-1) ∧
      ∀ D,HasDegreeHadamardSeedEncoding H r D → r-1≤D) := by sorry

theorem four_omitted_labels_degree_exact {d r : ℕ}
    (hr : 4≤r) (horder : d+1=2^r-4)
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ) (hH : Matrix.IsHadamard H)
    (hzero : ∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) :
    HasDegreeHadamardSeedEncoding H r (r-1) ∧
      ∀ D,HasDegreeHadamardSeedEncoding H r D → r-1≤D := by sorry


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


theorem punctured_reed_muller_radical_dimensions {r : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hproper : S≠Finset.univ) (hres : S.card%8=4) :
    let a := r-Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))
    let C := (lowDegreeBooleanCode r (r-2)).map (binaryFunctionRestriction S)
    Module.finrank (ZMod 2) C=S.card-a ∧
    Module.finrank (ZMod 2) (evenBinaryCode C)=S.card-a-1 ∧
    Module.finrank (ZMod 2) (binaryCodeRadical (evenBinaryCode C))=a+1 ∧
    binaryBilinearRank (evenBinaryCode C)=S.card-2*a-2 := by sorry


def bitSign (b : Bool) : ℤ := if b then -1 else 1

def IsUniformBinaryPairwiseIndependent {ι : Type*} [Fintype ι] {m : ℕ}
    (rows : ι → Fin m → Bool) : Prop :=
  (∀ i,(∑ z,bitSign (rows z i))=0) ∧
    (∀ i j,i≠j → (∑ z,bitSign (rows z i)*bitSign (rows z j))=0)


theorem punctured_observable_bounds {r D : ℕ} (hr : 4≤r)
    (S : Finset (Finset (Fin r))) (hN : 12≤S.card) (hres : S.card%8=4)
    (hproper : S≠Finset.univ)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r D)
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) :
    S.card-3≤∑ j∈Finset.range (D+1),Nat.choose r j ∧
    (2^(r-1)<S.card → r≤2*D) ∧
    (D≤r-2 → r-1≤Module.finrank (ZMod 2) (vectorSpan (ZMod 2) (omittedBooleanVectors S))) := by sorry

theorem four_omitted_punctured_encoding_impossible {r : ℕ} (hr : 5≤r)
    (S : Finset (Finset (Fin r))) (horder : S.card=2^r-4)
    (rows : S → Fin (S.card-4) → Bool) (hrows : IsUniformBinaryPairwiseIndependent rows)
    (f : Fin (S.card-4) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r (r-2))
    (hm : ∀ (i : Fin (S.card-4)) (z : S),f i z.val=if rows z i then 1 else 0) : False := by sorry

end
end EntropyDesigns
