/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators

def bitSign (b : Bool) : ℤ := if b then -1 else 1

def walshChar {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) : ℤ :=
  ∏ i ∈ S, bitSign (x i)

def collision {α : Type*} [Fintype α] (w : α → ℝ) : ℝ := ∑ a,w a^2

namespace SupportFace
abbrev BlockSeeds (k s : ℕ) := Fin k → (Fin s → Bool)
abbrev NonzeroMask (s : ℕ) := {S : Finset (Fin s) // S≠∅}
abbrev MixedBlock (k : ℕ) (i0 : Fin k) := {j : Fin k // j≠i0}
abbrev SourceCoordinate (k s : ℕ) (i0 : Fin k) := (Fin k × NonzeroMask s) ⊕ MixedBlock k i0
abbrev SourceOutcome (k s : ℕ) (i0 : Fin k) := SourceCoordinate k s i0 → Bool

def sourceSign {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    SourceCoordinate k s i0 → ℤ :=
  Sum.elim (fun a => walshChar a.2.val (x a.1))
    (fun j => walshChar e (x i0)*walshChar e (x j.val))
def sourceCode {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) : SourceOutcome k s i0 :=
  fun c => decide (sourceSign e i0 x c= -1)

def sourceFeasible {k s : ℕ} (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) : Prop :=
  (∀ y,0≤q y) ∧ (∑ y,q y=1) ∧
  (∀ c,(∑ y,q y*(bitSign (y c):ℝ))=0) ∧
  (∀ c d,c≠d → (∑ y,q y*(bitSign (y c):ℝ)*(bitSign (y d):ℝ))=0)
def sourceSupported {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) : Prop :=
  ∀ y,(¬∃ x,sourceCode e i0 x=y) → q y=0
def sourcePullback {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (q : SourceOutcome k s i0 → ℝ) :
    BlockSeeds k s → ℝ := fun x => q (sourceCode e i0 x)

end SupportFace

def seedMask {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)

noncomputable def uniformFiniteLaw {α : Type*} [DecidableEq α] (S : Finset α) (x : α) : ℝ :=
  if x∈S then 1/(S.card : ℝ) else 0

noncomputable def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1/2 : ℝ)*(∑ x,|p x-q x|)

namespace SupportWitness
variable {α : Type*} [Fintype α] [DecidableEq α]

def IsClique (R : α → α → Prop) (T : Finset α) : Prop :=
  ∀ a∈T,∀ b∈T,a≠b → R a b

def orthogonalityNumber (R : α → α → Prop) (S : Finset α) : ℕ := by
  classical
  exact S.powerset.sup fun T => if IsClique R T then T.card else 0

def blockLaws (R : α → α → Prop) (n : ℕ) : Set (α → ℝ) :=
  {q | ∃ T : Finset α,T.card=n ∧ IsClique R T ∧ q=uniformFiniteLaw T}

end SupportWitness
namespace SupportFace
open Filter
open scoped Topology

def observedOrthogonal {k s : ℕ} {i0 : Fin k} (x y : SourceOutcome k s i0) : Prop :=
  1+(∑ c : SourceCoordinate k s i0,bitSign (x c)*bitSign (y c))=0

def observedSupport {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) :
    Finset (SourceOutcome k s i0) := Finset.univ.image (sourceCode e i0)

abbrev OffsetParameters (k s : ℕ) (i0 : Fin k) := MixedBlock k i0 → (Fin s → Bool)

def seedXor {s : ℕ} (a b : Fin s → Bool) : Fin s → Bool := fun t => Bool.xor (a t) (b t)

def offsetSeed {k s : ℕ} (c : BlockSeeds k s) (a : Fin s → Bool) : BlockSeeds k s :=
  fun j => seedXor a (c j)

def extendOffsets {k s : ℕ} (i0 : Fin k) (c : OffsetParameters k s i0) : BlockSeeds k s :=
  fun j => if h : j=i0 then (fun _ => false) else c ⟨j,h⟩

def fullSourceRow {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k) (x : BlockSeeds k s) :
    Fin k × Finset (Fin s) → ℤ := fun a =>
  if a.2=∅ then walshChar e (x i0)*walshChar e (x a.1) else walshChar a.2 (x a.1)

def completedOffsetRow {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Fin k → Fin k → ℤ) (t : Fin k) (a : Fin s → Bool) :
    Fin k × Finset (Fin s) → ℤ :=
  fun z => K t z.1*fullSourceRow e i0 (offsetSeed c a) z

def offsetHadamard {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) :
    Matrix (Fin k × (Fin s → Bool)) (Fin k × (Fin s → Bool)) ℤ :=
  fun r z => completedOffsetRow e i0 c (fun i j => K i j) r.1 r.2 (z.1,seedMask z.2)

def fullColumnEquiv {k s : ℕ} (i0 : Fin k) :
    (Fin k × Finset (Fin s)) ≃ Option (SourceCoordinate k s i0) where
  toFun z := if hS : z.2=∅ then
    if hj : z.1=i0 then none else some (Sum.inr ⟨z.1,hj⟩)
    else some (Sum.inl (z.1,⟨z.2,hS⟩))
  invFun z := match z with
    | none => (i0,∅)
    | some (Sum.inl (j,S)) => (j,S.val)
    | some (Sum.inr j) => (j.val,∅)
  left_inv z := by
    rcases z with ⟨j,S⟩
    by_cases hS : S=∅
    · subst S
      by_cases hj : j=i0 <;> simp [hj]
    · simp [hS]
  right_inv z := by
    rcases z with _|z
    · simp
    · rcases z with ⟨j,S⟩|j
      · simp [S.property]
      · simp [j.property]

def completedCode {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (c : BlockSeeds k s) (K : Matrix (Fin k) (Fin k) ℤ) (t : Fin k) (a : Fin s → Bool) :
    SourceOutcome k s i0 := fun z => decide
      (completedOffsetRow e i0 c (fun i j => K i j) t a ((fullColumnEquiv i0).symm (some z))= -1)

def completedBlock {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (c : OffsetParameters k s i0) :
    Finset (SourceOutcome k s i0) := Finset.univ.image
      (fun r : Fin k × (Fin s → Bool) => completedCode e i0 (extendOffsets i0 c) K r.1 r.2)

def selectedEndpoint {k s : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (F : Finset (OffsetParameters k s i0)) :
    Finset (SourceOutcome k s i0) := Finset.univ.image
      (fun p : {c // c∈F} × (Fin k × (Fin s → Bool)) =>
        completedCode e i0 (extendOffsets i0 p.1.val) K p.2.1 p.2.2)

theorem uniform_source_sharp_distance {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ p : SourceOutcome k s i0 → ℝ,sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
      collision p=1/((2:ℝ)^s)^k ∧
      (∀ x : BlockSeeds k s,p (sourceCode e i0 x)=1/((2:ℝ)^s)^k) ∧
      (observedSupport e i0).card=(2^s)^k ∧
      (∀ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
          1-1/(k:ℝ)≤totalVariation p q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation p q=1-1/(k:ℝ)) := by sorry

theorem collision_preserving_exact_repair {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ K : Matrix (Fin k) (Fin k) ℤ,∃ F : Finset (OffsetParameters k s i0),
      Matrix.IsHadamard K ∧ (∀ j,K i0 j=1) ∧ (∀ t,K t i0=1) ∧
      F.card=(2^s)^k/(k*2^s) ∧
      sourceFeasible i0 (uniformFiniteLaw (observedSupport e i0)) ∧
      (selectedEndpoint e i0 K F).card=(2^s)^k ∧
      (observedSupport e i0∩selectedEndpoint e i0 K F).card=(2^s)^k/k ∧
      (∀ c∈F,Matrix.IsHadamard (offsetHadamard e i0 (extendOffsets i0 c) K)) ∧
      selectedEndpoint e i0 K F=F.biUnion (completedBlock e i0 K) ∧
      (∃ E : {x // x∈observedSupport e i0} ≃ {y // y∈selectedEndpoint e i0 K F},
        (∀ x,(E x).val=x.val ↔ x.val∈selectedEndpoint e i0 K F) ∧
        Fintype.card {x : {x // x∈observedSupport e i0} // (E x).val≠x.val}=
          (2^s)^k-(2^s)^k/k ∧
        ((Fintype.card {x : {x // x∈observedSupport e i0} // (E x).val≠x.val}:ℕ):ℝ)=
          (((2^s)^k:ℕ):ℝ)*(1-1/(k:ℝ))) ∧
      collision (uniformFiniteLaw (observedSupport e i0))=1/(((2^s)^k:ℕ):ℝ) ∧
      collision (uniformFiniteLaw (selectedEndpoint e i0 K F))=1/(((2^s)^k:ℕ):ℝ) := by sorry

theorem source_all_repairs_lower {k s b : ℕ} (e : Finset (Fin s)) (i0 : Fin k)
    (hsize : 2*(k-1)<2^s)
    (x y : Fin b → Fin (k*2^s) → SourceOutcome k s i0)
    (hx : ∀ j i,x j i∈observedSupport e i0)
    (horth : ∀ j i l,i≠l → observedOrthogonal (y j i) (y j l)) :
    ((b*(k*2^s):ℕ):ℝ)*(1-1/(k:ℝ))≤
      ∑ j : Fin b,((Finset.univ.filter (fun i => x j i≠y j i)).card:ℝ) := by sorry

theorem sharp_distance_tends_to_one :
    Tendsto (fun r : ℕ => 1-1/(2:ℝ)^r) atTop (nhds (1:ℝ)) := by sorry

end SupportFace
end
end EntropyDesigns
