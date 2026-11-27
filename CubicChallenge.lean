/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators Matrix

def squarefreeBooleanMonomial {ι : Type*} [DecidableEq ι]
    (s z : Finset ι) : ZMod 2 := if s ⊆ z then 1 else 0

def lowDegreeBooleanCode (r d : ℕ) : Submodule (ZMod 2) (Finset (Fin r) → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun s : {s : Finset (Fin r) // s.card≤d} =>
    squarefreeBooleanMonomial s.val))

def booleanValueSign (a : ZMod 2) : ℤ := if a=0 then 1 else -1

def squarefreeBooleanPolynomial {r : ℕ} (terms : Finset (Finset (Fin r)))
    (z : Finset (Fin r)) : ZMod 2 := ∑ s∈terms,squarefreeBooleanMonomial s z

def naturalMaskSupport (r mask : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => Nat.testBit mask i.val)

def polynomialMaskTerms (r : ℕ) (masks : List ℕ) : Finset (Finset (Fin r)) :=
  (masks.map (naturalMaskSupport r)).toFinset

def bitHadamardSign {n : ℕ} (masks : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if Nat.testBit (masks i) j.val then -1 else 1

def benchmarkRowMask12 : Fin 12 → ℕ := ![0,2954,1814,3628,3162,2230,366,732,1464,2928,1762,3524]

def benchmarkHadamard12 : Matrix (Fin 12) (Fin 12) ℤ := bitHadamardSign benchmarkRowMask12

def benchmarkLabelMask12 : Fin 12 → ℕ := ![0,5,3,6,13,11,7,14,4,8,1,2]

def benchmarkLabels12 (j : Fin 12) : Finset (Fin 4) := naturalMaskSupport 4 (benchmarkLabelMask12 j)

def benchmarkPolynomialMasks12 : Fin 11 → List ℕ := ![[1],[2],[4],[3,4,5,6,8,11],[1,3,4,8,9,11],[1,2,5,6,7,8,11],[1,2,4,5,9,10,11],[2,4,7,8,10,11],[1,6,8,10,11],[1,2,3,4,6,7,9,10,11],[2,3,5,7,8,9,11]]

def benchmarkPolynomial12 (i : Fin 11) : Finset (Fin 4) → ZMod 2 :=
 squarefreeBooleanPolynomial (polynomialMaskTerms 4 (benchmarkPolynomialMasks12 i))

def benchmarkRowMask20 : Fin 20 → ℕ := ![0,649754,250934,501868,1003736,958898,869222,689870,331166,662332,276090,552180,55786,111572,223144,446288,892576,736578,424582,849164]

def benchmarkHadamard20 : Matrix (Fin 20) (Fin 20) ℤ := bitHadamardSign benchmarkRowMask20

def benchmarkLabelMask20 : Fin 20 → ℕ := ![0,13,27,22,12,25,19,7,15,30,29,26,21,10,20,8,16,1,3,6]

def benchmarkLabels20 (j : Fin 20) : Finset (Fin 5) := naturalMaskSupport 5 (benchmarkLabelMask20 j)

def benchmarkPolynomialMasks20 : Fin 19 → List ℕ := ![[1],[2],[4],[8],[16],[1,3,4,6,7,8,12,14,19,20],[3,5,7,9,10,12,13,16,17,18],[1,2,4,5,6,7,8,9,10,13,14,18],[3,4,5,6,7,8,16,19,20],[1,2,7,8,9,11,12,16,19],[1,4,6,7,8,9,10,11,13,16],[1,2,3,4,6,7,11,14,16],[1,4,10,11,12,14,19],[2,4,5,6,8,11,12,13,17,18],[2,3,7,8,10,11,12,13,16,17,20],[1,3,10,11,12,13,14,16],[1,2,3,5,6,8,13,14,17,20],[2,4,6,7,8,9,11,12,14,16,18],[1,3,4,5,7,9,13,14,16]]

def benchmarkPolynomial20 (i : Fin 19) : Finset (Fin 5) → ZMod 2 :=
 squarefreeBooleanPolynomial (polynomialMaskTerms 5 (benchmarkPolynomialMasks20 i))

def NoQuadraticHadamardSeedEncoding (d r : ℕ) : Prop :=
  ∀ H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ,Matrix.IsHadamard H → (∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) →
  ∀ labels : Fin (d+1) → Finset (Fin r),Function.Injective labels →
  ∀ f : Fin d → (Finset (Fin r) → ZMod 2),
    (∀ j i,booleanValueSign (f i (labels j))=H j i.succ) →
    ¬(∀ i,f i∈lowDegreeBooleanCode r 2)

def HasAffineSeedExtension {N r : ℕ} (labels : Fin N → Finset (Fin r))
    (g : Finset (Fin r) → ZMod 2) : Prop :=
  ∃ h∈lowDegreeBooleanCode r 1,∀ j,h (labels j)=g (labels j)

open scoped Classical in
def IsExactCubicSeedBenchmark {d r : ℕ}
    (H : Matrix (Fin (d+1)) (Fin (d+1)) ℤ)
    (labels : Fin (d+1) → Finset (Fin r))
    (f : Fin d → (Finset (Fin r) → ZMod 2)) (affineCount : ℕ) : Prop :=
  Matrix.IsHadamard H ∧ (∀ j,H j ⟨0,Nat.zero_lt_succ d⟩=1) ∧ Function.Injective labels ∧
  (∀ i,f i∈lowDegreeBooleanCode r 3) ∧
  (∀ j i,booleanValueSign (f i (labels j))=H j i.succ) ∧
  (Finset.univ.filter (fun i => HasAffineSeedExtension labels (f i))).card=affineCount

theorem sharp_cubic_seed_benchmarks :
    NoQuadraticHadamardSeedEncoding 11 4 ∧ NoQuadraticHadamardSeedEncoding 19 5 ∧
    IsExactCubicSeedBenchmark (d:=11) (r:=4) benchmarkHadamard12 benchmarkLabels12 benchmarkPolynomial12 3 ∧
    IsExactCubicSeedBenchmark (d:=19) (r:=5) benchmarkHadamard20 benchmarkLabels20 benchmarkPolynomial20 5 := by sorry

end
end EntropyDesigns
