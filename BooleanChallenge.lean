module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def squarefreeBooleanMonomial {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) : ZMod 2 := if s ⊆ z then 1 else 0

def lowDegreeBooleanCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun s : {s : Finset (Fin r) // s.card≤d} =>
    squarefreeBooleanMonomial s.val))

def booleanCubeDotForm (r : ℕ) :
    LinearMap.BilinForm (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  dotProductBilin (ZMod 2) (ZMod 2)

def binaryFunctionRestriction {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (ι → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2) where
  toFun f := fun z => f z.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def booleanSupportVector {r : ℕ} (z : Finset (Fin r)) : Fin r → ZMod 2 :=
  fun i => if i∈z then 1 else 0

theorem lowDegreeBooleanCode_finrank (r d : ℕ) :
    Module.finrank (ZMod 2) (lowDegreeBooleanCode r d)=
      Fintype.card {s : Finset (Fin r) // s.card≤d} := by sorry

theorem lowDegreeBooleanCode_duality {r d : ℕ} (hd : d<r) :
    (booleanCubeDotForm r).orthogonal (lowDegreeBooleanCode r d)=
      lowDegreeBooleanCode r (r-d-1) := by sorry

theorem lowDegreeBooleanCode_extension_criterion {r d : ℕ} (hd : d<r)
    (S : Finset (Finset (Fin r))) :
    (∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r d, binaryFunctionRestriction S g=f) ↔
      (∀ g∈lowDegreeBooleanCode r (r-d-1), (∀ z,z∉S → g z=0) → g=0) := by sorry

theorem four_bit_cubic_extension (S : Finset (Finset (Fin 4))) (hproper : S≠Finset.univ) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode 4 3, binaryFunctionRestriction S g=f := by sorry

theorem five_bit_affine_complement_cubic_extension
    (S : Finset (Finset (Fin 5)))
    (hspan : affineSpan (ZMod 2) (Set.range (fun z : {z : Finset (Fin 5) // z∉S} =>
      booleanSupportVector z.val))=⊤) :
    ∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode 5 3, binaryFunctionRestriction S g=f := by sorry


def IsBinaryStrengthTwo {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop :=
  ∀ i j,i≠j → ∀ a b : Bool,
    4*(Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)).card=N

def binaryObservationMatrix {N d : ℕ} (rows : Fin N → Fin d → Bool) :
    Matrix (Fin N) (Fin d) (ZMod 2) := fun r i => if rows r i then 1 else 0

def booleanDegreeDualCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  if d<r then lowDegreeBooleanCode r (r-d-1) else ⊥

theorem booleanSupport_extension_criterion_all_degrees (r d : ℕ)
    (S : Finset (Finset (Fin r))) :
    (∀ f : S → ZMod 2, ∃ g∈lowDegreeBooleanCode r d, binaryFunctionRestriction S g=f) ↔
      (∀ g∈booleanDegreeDualCode r d, (∀ z,z∉S → g z=0) → g=0) := by sorry

theorem minimal_binary_seed_growing_degree {N r d : ℕ}
    (hN : 12≤N) (hres : N%8=4) (hlo : 2^(r-1)<N) (hhi : N≤2^r)
    (labels : Fin N → Finset (Fin r)) (hinj : Function.Injective labels)
    (rows : Fin N → Fin (N-2) → Bool) (hOA : IsBinaryStrengthTwo rows)
    (f : Fin (N-2) → (Finset (Fin r) → ZMod 2))
    (hf : ∀ i,f i∈lowDegreeBooleanCode r d)
    (hmatch : ∀ i j,f i (labels j)=binaryObservationMatrix rows j i) :
    r≤2*d ∧ (∀ y : Fin N → ZMod 2, ∃ g∈lowDegreeBooleanCode r (r-1), ∀ j,g (labels j)=y j) := by sorry

end
end EntropyDesigns
