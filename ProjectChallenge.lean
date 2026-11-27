/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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

end SupportFace
def binarySeed {d : ℕ} (x : Fin d → Bool) : Fin d → ZMod 2 :=
  fun i => if x i then 1 else 0

theorem binarySeed_bijective {d : ℕ} : Function.Bijective (@binarySeed d) := by sorry

namespace SupportFace
def boolBinaryEquiv (s : ℕ) : (Fin s → Bool) ≃ (Fin s → ZMod 2) :=
  Equiv.ofBijective binarySeed binarySeed_bijective

def fieldCoordinates (s : ℕ) (hs : s≠0) : GaloisField 2 s ≃ₗ[ZMod 2] (Fin s → ZMod 2) :=
  LinearEquiv.ofFinrankEq (R:=ZMod 2) (GaloisField 2 s) (Fin s → ZMod 2)
    (by rw [GaloisField.finrank 2 hs,Module.finrank_fin_fun])

def fieldSeedEquiv (s : ℕ) (hs : s≠0) : GaloisField 2 s ≃ (Fin s → Bool) :=
  (fieldCoordinates s hs).toEquiv.trans (boolBinaryEquiv s).symm

section
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]
def slopeMap (t : F) : (F × F) →ₗ[ZMod 2] F where
  toFun p := p.1+t*p.2
  map_add' p q := by simp [mul_add];ring
  map_smul' c p := by simp [Algebra.smul_def];ring

end
def fieldSlopeSeeds {k s : ℕ} (hs : s≠0) (t : Fin k → GaloisField 2 s)
    (p : GaloisField 2 s × GaloisField 2 s) : BlockSeeds k s :=
  fun i => fieldSeedEquiv s hs (slopeMap (t i) p)

end SupportFace
namespace ConcentratedFamily
open SupportFace Filter
open scoped Topology
def fieldOffsetParameters {k s : ℕ} (hs : s≠0) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (B : GaloisField 2 s) : OffsetParameters k s i0 :=
  fun j => fieldSeedEquiv s hs ((t j.val-t i0)*B)

def fieldOffsetImage {k s : ℕ} (hs : s≠0) (i0 : Fin k) (t : Fin k → GaloisField 2 s) :
    Finset (OffsetParameters k s i0) := by
  classical
  exact Finset.univ.filter (fun c => ∃ B,fieldOffsetParameters hs i0 t B=c)

def planeSupport {k s : ℕ} (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) : Finset (SourceOutcome k s i0) := by
  classical
  exact Finset.univ.filter (fun y => ∃ p : GaloisField 2 s × GaloisField 2 s,
    sourceCode e i0 (fieldSlopeSeeds hs t p)=y)

theorem concentrated_witness_exists {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ hs : s≠0,∃ t : Fin k → GaloisField 2 s,Function.Injective t ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
      sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
      (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
      (∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → sourceSupported e i0 q → collision q≤collision p) ∧
      (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
        ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
          ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
        (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
        collision p/collision q=(k:ℝ)/(2:ℝ)^s) := by sorry

theorem concentrated_sharp_distance {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (hs : s≠0) (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    (∀ q : SourceOutcome k s i0 → ℝ,
      q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
        1-1/(k:ℝ)≤totalVariation (uniformFiniteLaw (planeSupport hs e i0 t)) q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation (uniformFiniteLaw (planeSupport hs e i0 t)) q=1-1/(k:ℝ)) := by sorry

theorem concentrated_exact_repair {k s : ℕ} (hk : 2≤k) (r : ℕ) (hkpow : k=2^r)
    (hsize : 2*(k-1)<2^s) (hs : s≠0) (e : Finset (Fin s)) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    ∃ K : Matrix (Fin k) (Fin k) ℤ,Matrix.IsHadamard K ∧
      (∀ j,K i0 j=1) ∧ (∀ a,K a i0=1) ∧
      ∃ G : Finset (OffsetParameters k s i0),G⊆fieldOffsetImage hs i0 t ∧ G.card=2^s/k ∧
        (selectedEndpoint e i0 K G).card=(2^s)^2 ∧
        (planeSupport hs e i0 t∩selectedEndpoint e i0 K G).card=(2^s)^2/k ∧
        (∀ c∈G,Matrix.IsHadamard (offsetHadamard e i0 (extendOffsets i0 c) K)) ∧
        selectedEndpoint e i0 K G=G.biUnion (completedBlock e i0 K) ∧
        (∃ E : {x // x∈planeSupport hs e i0 t} ≃ {y // y∈selectedEndpoint e i0 K G},
          (∀ x,(E x).val=x.val ↔ x.val∈selectedEndpoint e i0 K G) ∧
          Fintype.card {x : {x // x∈planeSupport hs e i0 t} // (E x).val≠x.val}=
            (2^s)^2-(2^s)^2/k ∧
          ((Fintype.card {x : {x // x∈planeSupport hs e i0 t} // (E x).val≠x.val}:ℕ):ℝ)=
            (((2^s)^2:ℕ):ℝ)*(1-1/(k:ℝ))) ∧
        collision (uniformFiniteLaw (planeSupport hs e i0 t))=1/((2:ℝ)^s)^2 ∧
        collision (uniformFiniteLaw (selectedEndpoint e i0 K G))=1/((2:ℝ)^s)^2 := by sorry

theorem concentrated_all_repairs_lower {k s b : ℕ} (hsize : 2*(k-1)<2^s) (hs : s≠0)
    (e : Finset (Fin s)) (i0 : Fin k) (t : Fin k → GaloisField 2 s)
    (x y : Fin b → Fin (k*2^s) → SourceOutcome k s i0)
    (hx : ∀ j i,x j i∈planeSupport hs e i0 t)
    (horth : ∀ j i l,i≠l → observedOrthogonal (y j i) (y j l)) :
    ((b*(k*2^s):ℕ):ℝ)*(1-1/(k:ℝ))≤
      ∑ j : Fin b,((Finset.univ.filter (fun i => x j i≠y j i)).card:ℝ) := by sorry

theorem concentrated_canonical_limits :
    (∀ r : ℕ,1≤r → 2≤2^r ∧ 2*((2^r)-1)<2^(2*r) ∧ 2^(2*r)=(2^r)^2) ∧
      (∀ r : ℕ,(1/((2:ℝ)^(2*r))^2)/(1/((2^r*2^(2*r):ℕ):ℝ))=1/(2:ℝ)^r) ∧
      Tendsto (fun r : ℕ =>
        ((1/((2:ℝ)^(2*r))^2)/(1/((2^r*2^(2*r):ℕ):ℝ)),1-1/(2:ℝ)^r))
        atTop (nhds ((0:ℝ),(1:ℝ))) := by sorry

end ConcentratedFamily
namespace SpanningSlopes
open SupportFace ConcentratedFamily
theorem spanning_slope_data_exists {k s : ℕ} (hs : s≠0)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2) (i0 : Fin k) :
    k<2^s ∧ ∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) := by sorry

theorem spanning_slopes_orthogonal_iff {k s : ℕ} (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2)
    (p q : GaloisField 2 s × GaloisField 2 s) (hpq : p≠q) :
    observedOrthogonal (sourceCode e i0 (fieldSlopeSeeds hs t p))
      (sourceCode e i0 (fieldSlopeSeeds hs t q)) ↔ p.2=q.2 := by sorry

theorem spanning_plane_code_injective {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (i0 : Fin k) (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    Function.Injective (fun p : GaloisField 2 s × GaloisField 2 s =>
      sourceCode e i0 (fieldSlopeSeeds hs t p)) := by sorry

theorem spanning_plane_orthogonality_number {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) :
    SupportWitness.orthogonalityNumber observedOrthogonal (ConcentratedFamily.planeSupport hs e i0 t)=2^s := by sorry

theorem source_optimizer_of_known_hadamard {k s : ℕ} (i0 : Fin k)
    (e : Finset (Fin s)) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
      (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) := by sorry

theorem spanning_plane_full_properties {k s : ℕ} (hk : 2≤k) (hkh : k<2^s) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) (hzero : t i0=0)
    (R : Finset (GaloisField 2 s))
    (hspan : Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤)
    (hcomp : ∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a)
    (hsmall : R.card<2^s/2) (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    let p := uniformFiniteLaw (planeSupport hs e i0 t)
    sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
      (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
      (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
        ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
          ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
        (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
        collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
      (∀ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
          1-1/(k:ℝ)≤totalVariation p q) ∧
      (∃ q : SourceOutcome k s i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
          totalVariation p q=1-1/(k:ℝ)) := by sorry

theorem spanning_witness_exists {k s : ℕ} (hk : 2≤k)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    ∃ hs : s≠0,∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
      sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
        (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
        (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
          ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
            ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
        (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
          (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
          collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
        (∀ q : SourceOutcome k s i0 → ℝ,
          q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
            1-1/(k:ℝ)≤totalVariation p q) ∧
        (∃ q : SourceOutcome k s i0 → ℝ,
          q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
            totalVariation p q=1-1/(k:ℝ)) := by sorry

end SpanningSlopes
end
end EntropyDesigns

namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily
open Filter
open scoped Topology
def FullSpanningWitness (k s : ℕ) (e : Finset (Fin s)) (i0 : Fin k) : Prop :=
  ∃ hs : s≠0,∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
      sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
        (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
        (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
          ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
            ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
        (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
          (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
          collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
        (∀ q : SourceOutcome k s i0 → ℝ,
          q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
            1-1/(k:ℝ)≤totalVariation p q) ∧
        (∃ q : SourceOutcome k s i0 → ℝ,
          q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
            totalVariation p q=1-1/(k:ℝ))

theorem inverse_order_tends_zero (k h : ℕ → ℕ) (hk : ∀ i,0<k i)
    (hkh : ∀ i,k i<h i)
    (hratio : Tendsto (fun i => (k i:ℝ)/(h i:ℝ)) atTop (nhds 1)) :
    Tendsto (fun i => 1/(k i:ℝ)) atTop (nhds 0) := by sorry

theorem sharp_distance_tends_one (k h : ℕ → ℕ) (hk : ∀ i,0<k i)
    (hkh : ∀ i,k i<h i)
    (hratio : Tendsto (fun i => (k i:ℝ)/(h i:ℝ)) atTop (nhds 1)) :
    Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) := by sorry

theorem entropy_scale_tends_zero (k h : ℕ → ℕ)
    (hratio : Tendsto (fun i => (k i:ℝ)/(h i:ℝ)) atTop (nhds 1)) :
    Tendsto (fun i => Real.log ((h i:ℝ)/(k i:ℝ))) atTop (nhds 0) := by sorry

theorem collision_deficit_identity {k h : ℕ} (hk : 0<k) (hh : 0<h) (hkh : k≤h) :
    1/((k*h:ℕ):ℝ)-1/((h^2:ℕ):ℝ)=((h-k:ℕ):ℝ)/((k*h^2:ℕ):ℝ) := by sorry

theorem selected_hadamard_orders :
    ∃ a s : ℕ → ℕ,
      (∀ i, i ≤ a i) ∧
      (∀ i, s i ≤ 2^(s i) - 12^(a i)) ∧
      (∀ i, 12^(a i) < 2^(s i) ∧ 2^(s i) < 2 * 12^(a i)) ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i))) (Fin (12^(a i))) ℤ,
        Matrix.IsHadamard H) ∧
      Tendsto (fun i => ((12^(a i) : ℕ) : ℝ) / ((2^(s i) : ℕ) : ℝ))
        atTop (nhds 1) := by sorry

theorem selected_order_limits :
    ∃ a s : ℕ → ℕ,
      (∀ i, i ≤ a i) ∧
      (∀ i, s i ≠ 0 ∧ s i ≤ 2^(s i)-12^(a i) ∧
        2^(s i)-12^(a i) < 2^(s i)/2) ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i))) (Fin (12^(a i))) ℤ,
        Matrix.IsHadamard H) ∧
      Tendsto (fun i => ((12^(a i) : ℕ) : ℝ) / ((2^(s i) : ℕ) : ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => 1-1/((12^(a i) : ℕ) : ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => Real.log (((2^(s i) : ℕ) : ℝ) / ((12^(a i) : ℕ) : ℝ)))
        atTop (nhds 0) := by sorry

theorem relative_spanning_laws (k s : ℕ → ℕ)
    (hk : ∀ i, 2 ≤ k i) (hsu : ∀ i, s i ≤ 2^(s i)-k i)
    (hsmall : ∀ i, 2^(s i)-k i < 2^(s i)/2)
    (hK : ∀ i, ∃ K : Matrix (Fin (k i)) (Fin (k i)) ℤ, Matrix.IsHadamard K)
    (hratio : Tendsto (fun i => (k i:ℝ)/((2^(s i):ℕ):ℝ)) atTop (nhds 1)) :
    (∀ i, ∃ e : Finset (Fin (s i)), ∃ i0 : Fin (k i),
      e.Nonempty ∧ FullSpanningWitness (k i) (s i) e i0) ∧
    Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) ∧
    (∀ i, 1/((k i*2^(s i):ℕ):ℝ)-1/(((2^(s i))^2:ℕ):ℝ)=
      ((2^(s i)-k i:ℕ):ℝ)/((k i*(2^(s i))^2:ℕ):ℝ)) := by sorry

end
end EntropyDesigns.RelativeSequence

namespace EntropyDesigns
open scoped BigOperators
noncomputable def shannon {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -(∑ a, w a * Real.log (w a))
end EntropyDesigns

namespace EntropyDesigns.RelativeSequence
noncomputable section
open SupportFace ConcentratedFamily SpanningSlopes
open Filter Set
open scoped Topology BigOperators
def renyiOffOne {A : Type*} [Fintype A] (w : A → ℝ) (α : ℝ) : ℝ :=
  Real.log (∑ x, (w x)^α) / (1-α)


def renyiEntropy {A : Type*} [Fintype A] (w : A → ℝ) (α : ℝ) : ℝ :=
  if α = 1 then shannon w else renyiOffOne w α

def maxWeight {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w

def minEntropy {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ) : ℝ :=
  -Real.log (maxWeight w)


def CompleteSpanningWitness (k s : ℕ) (e : Finset (Fin s)) (i0 : Fin k) : Prop :=
  ∃ hs : s≠0,∃ R : Finset (GaloisField 2 s),∃ t : Fin k → GaloisField 2 s,
      Function.Injective t ∧ t i0=0 ∧ R.card=2^s-k ∧ 0∉R ∧
      Submodule.span (ZMod 2) (R:Set (GaloisField 2 s))=⊤ ∧
      (∀ a : GaloisField 2 s,a∈R ↔ ¬∃ j : Fin k,t j=a) ∧
      let p := uniformFiniteLaw (planeSupport hs e i0 t)
      (sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
        (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
        (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
          ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
            ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
        (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
          (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
          collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
        (∀ q : SourceOutcome k s i0 → ℝ,
          q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
            1-1/(k:ℝ)≤totalVariation p q) ∧
        (∃ q : SourceOutcome k s i0 → ℝ,
          q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
            totalVariation p q=1-1/(k:ℝ))) ∧
    p ∈ Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q} ∧
    (∃ q : SourceOutcome k s i0 → ℝ, sourceFeasible i0 q ∧
      (∀ α : ℝ, 0<α →
        (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w →
          renyiEntropy q α ≤ renyiEntropy w α) ∧
        renyiEntropy p α - renyiEntropy q α = Real.log ((2:ℝ)^s/(k:ℝ))) ∧
      (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w → minEntropy q ≤ minEntropy w) ∧
      minEntropy p - minEntropy q = Real.log ((2:ℝ)^s/(k:ℝ)))


structure CompleteLawData (k s : ℕ) where
  e : Finset (Fin s)
  he : e.Nonempty
  i0 : Fin k
  hs : s≠0
  t : Fin k → GaloisField 2 s
  ht : Function.Injective t
  properties :
    let p := uniformFiniteLaw (planeSupport hs e i0 t);
          sourceFeasible i0 p ∧ sourceSupported e i0 p ∧
            (planeSupport hs e i0 t).card=(2^s)^2 ∧ collision p=1/((2:ℝ)^s)^2 ∧
            (0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
              ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
                ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p) ∧
            (∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ collision q=1/((k*2^s:ℕ):ℝ) ∧
              (∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision q) ∧
              collision p/collision q=(k:ℝ)/(2:ℝ)^s) ∧
            (∀ q : SourceOutcome k s i0 → ℝ,
              q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) →
                1-1/(k:ℝ)≤totalVariation p q) ∧
            (∃ q : SourceOutcome k s i0 → ℝ,
              q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k*2^s)) ∧
                totalVariation p q=1-1/(k:ℝ))

  vertex : uniformFiniteLaw (planeSupport hs e i0 t) ∈
    Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q}
  optimizer : SourceOutcome k s i0 → ℝ
  optimizer_feasible : sourceFeasible i0 optimizer
  optimizer_collision : collision optimizer=1/((k*2^s:ℕ):ℝ)
  optimizer_global : ∀ w : SourceOutcome k s i0 → ℝ,sourceFeasible i0 w → collision w≤collision optimizer
  ratio : collision (uniformFiniteLaw (planeSupport hs e i0 t))/collision optimizer=(k:ℝ)/(2:ℝ)^s
  entropy_optimizer : ∀ α : ℝ,0<α → renyiEntropy optimizer α=Real.log ((k*2^s:ℕ):ℝ)
  minentropy_optimizer : minEntropy optimizer=Real.log ((k*2^s:ℕ):ℝ)
  entropy_excess : ∀ α : ℝ,0<α →
    renyiEntropy (uniformFiniteLaw (planeSupport hs e i0 t)) α-renyiEntropy optimizer α=
      Real.log ((2:ℝ)^s/(k:ℝ))
  minentropy_excess : minEntropy (uniformFiniteLaw (planeSupport hs e i0 t))-minEntropy optimizer=
    Real.log ((2:ℝ)^s/(k:ℝ))

def CompleteLawData.law {k s : ℕ} (D : CompleteLawData k s) : SourceOutcome k s D.i0 → ℝ :=
  uniformFiniteLaw (planeSupport D.hs D.e D.i0 D.t)


theorem renyi_all_lower {A : Type*} [Fintype A] (w : A → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hcap : ∀ x, w x ≤ 1/N) :
    Real.log N ≤ renyiEntropy w α := by sorry

theorem renyi_all_uniform {A : Type*} [Fintype A] (w : A → ℝ)
    (N α : ℝ) (hN : 0 < N) (hα : 0 < α) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) : renyiEntropy w α = Real.log N := by sorry

theorem minEntropy_lower {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (hmass : ∑ x, w x = 1) (N : ℝ) (hN : 0 < N)
    (hcap : ∀ x, w x ≤ 1/N) : Real.log N ≤ minEntropy w := by sorry

theorem minEntropy_uniform {A : Type*} [Fintype A] [Nonempty A] (w : A → ℝ)
    (N : ℝ) (hN : 0 < N) (hmass : ∑ x, w x = 1)
    (huniform : ∀ x, w x = 0 ∨ w x = 1/N) : minEntropy w = Real.log N := by sorry

theorem plane_entropy_excess {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    let p := uniformFiniteLaw (planeSupport hs e i0 t)
    ∃ q : SourceOutcome k s i0 → ℝ, sourceFeasible i0 q ∧
      (∀ α : ℝ, 0<α →
        (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w →
          renyiEntropy q α ≤ renyiEntropy w α) ∧
        renyiEntropy p α - renyiEntropy q α = Real.log ((2:ℝ)^s/(k:ℝ))) ∧
      (∀ w : SourceOutcome k s i0 → ℝ, sourceFeasible i0 w → minEntropy q ≤ minEntropy w) ∧
      minEntropy p - minEntropy q = Real.log ((2:ℝ)^s/(k:ℝ)) := by sorry

theorem plane_uniform_vertex {k s : ℕ} (hk : 2≤k) (hs : s≠0)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (t : Fin k → GaloisField 2 s) (ht : Function.Injective t) :
    uniformFiniteLaw (planeSupport hs e i0 t) ∈
      Set.extremePoints ℝ {q : SourceOutcome k s i0 → ℝ | sourceFeasible i0 q} := by sorry

theorem complete_spanning_witness_exists {k s : ℕ} (hk : 2≤k)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    CompleteSpanningWitness k s e i0 := by sorry

theorem complete_law_data_exists {k s : ℕ} (hk : 2≤k)
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    Nonempty (CompleteLawData k s) := by sorry

theorem known_scaled_hadamard_exists {k s : ℕ} (i0 : Fin k)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    ∃ H : Matrix (Fin (k*2^s)) (Fin (k*2^s)) ℤ,Matrix.IsHadamard H := by sorry

theorem full_unconditional_sequence :
    ∃ a s : ℕ → ℕ, ∃ D : (i : ℕ) → CompleteLawData (12^(a i)) (s i),
      Tendsto (fun i => 12^(a i)*2^(s i)) atTop atTop ∧
      (∀ i, ∃ H : Matrix (Fin (12^(a i)*2^(s i))) (Fin (12^(a i)*2^(s i))) ℤ,
        Matrix.IsHadamard H) ∧
      (∀ i, sourceFeasible (D i).i0 (D i).law ∧
        (D i).law ∈ Set.extremePoints ℝ
          {q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ | sourceFeasible (D i).i0 q}) ∧
      Tendsto (fun i => collision (D i).law / collision (D i).optimizer) atTop (nhds 1) ∧
      Tendsto (fun i => ((12^(a i)*2^(s i):ℕ):ℝ) * collision (D i).law) atTop (nhds 1) ∧
      (∀ i, ∀ q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (12^(a i)*2^(s i))) →
          1-1/((12^(a i):ℕ):ℝ) ≤ totalVariation (D i).law q) ∧
      (∀ i, ∃ q : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (12^(a i)*2^(s i))) ∧
          totalVariation (D i).law q=1-1/((12^(a i):ℕ):ℝ)) ∧
      Tendsto (fun i => 1-1/((12^(a i):ℕ):ℝ)) atTop (nhds 1) ∧
      (∀ α : ℝ, 0<α →
        (∀ i, ∀ w : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
          sourceFeasible (D i).i0 w → renyiEntropy (D i).optimizer α ≤ renyiEntropy w α) ∧
        Tendsto (fun i => renyiEntropy (D i).law α-renyiEntropy (D i).optimizer α)
          atTop (nhds 0)) ∧
      (∀ i, ∀ w : SourceOutcome (12^(a i)) (s i) (D i).i0 → ℝ,
        sourceFeasible (D i).i0 w → minEntropy (D i).optimizer ≤ minEntropy w) ∧
      Tendsto (fun i => minEntropy (D i).law-minEntropy (D i).optimizer) atTop (nhds 0) := by sorry

end
end EntropyDesigns.RelativeSequence

namespace EntropyDesigns.RelativeSequence
theorem spanning_summary_input {k s : ℕ}
    (hsu : s≤2^s-k) (hsmall : 2^s-k<2^s/2)
    (K : Matrix (Fin k) (Fin k) ℤ) (hK : Matrix.IsHadamard K) :
    Nonempty (CompleteLawData k s) := by sorry
end EntropyDesigns.RelativeSequence

namespace EntropyDesigns.Concentration
noncomputable section
open SupportFace
def observedAtoms {k s : ℕ} {i0 : Fin k} (p : SourceOutcome k s i0 → ℝ) :
    Finset (SourceOutcome k s i0) := Finset.univ.filter (fun y => p y≠0)


end
end EntropyDesigns.Concentration

namespace EntropyDesigns.GapTransfer
noncomputable section
open Filter Asymptotics Set RelativeSequence SupportFace
open scoped Topology
def dyadicBuffer (G : ℝ → ℝ) (s : ℕ) : ℝ := G ((2:ℝ)^s)+(s:ℝ)+1


def knownHadamardOrder (n : ℕ) : Prop :=
  ∃ H : Matrix (Fin n) (Fin n) ℤ,Matrix.IsHadamard H

def uniformGapInput (G : ℝ → ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop,∃ k : ℕ,knownHadamardOrder k ∧ x-G x≤(k:ℝ) ∧ (k:ℝ)≤x

/-- The complete finite-law witness is selected from exactly the paper's
uniform known-order gap hypothesis; no new Hadamard existence input is
silently assumed. The quantitative asymptotic rates are separate. -/

theorem dyadic_order_tends_infinity : Tendsto (fun s : ℕ => (2:ℝ)^s) atTop atTop := by sorry

theorem dyadic_buffer_ratio_zero (G : ℝ → ℝ) (hG : G =o[atTop] (fun x : ℝ => x)) :
    Tendsto (fun s : ℕ => dyadicBuffer G s/(2:ℝ)^s) atTop (nhds 0) := by sorry

theorem dyadic_buffer_positive (G : ℝ → ℝ)
    (hG : ∀ x : ℝ,0≤x → 0≤G x) (s : ℕ) : 0<dyadicBuffer G s := by sorry

theorem dyadic_buffer_eventually_small (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x)) :
    ∀ᶠ s : ℕ in atTop,3*dyadicBuffer G s<(2:ℝ)^s/2 := by sorry

theorem shifted_dyadic_tends_infinity (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) :
    Tendsto (fun s : ℕ => (2:ℝ)^s-2*dyadicBuffer G s) atTop atTop := by sorry

theorem buffered_hadamard_order_exists (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) (hmono : MonotoneOn G (Ici 0))
    (hgap : uniformGapInput G) :
    ∀ᶠ s : ℕ in atTop,∃ k : ℕ,knownHadamardOrder k ∧
      2*dyadicBuffer G s≤(2:ℝ)^s-(k:ℝ) ∧
      (2:ℝ)^s-(k:ℝ)≤3*dyadicBuffer G s ∧
      s≤2^s-k ∧ 2^s-k<2^s/2 ∧ Nonempty (RelativeSequence.CompleteLawData k s) := by sorry

theorem gap_rate_bounds (h k A : ℝ) (hh : 0<h) (ha : 0≤A)
    (hhalf : h/2<k) (hkh : k<h) (hlow : 2*A≤h-k) (hupp : h-k≤3*A) :
    (2*A/h≤1-k/h ∧ 1-k/h≤3*A/h) ∧
    (2*A/h^3≤1/(k*h)-1/h^2 ∧ 1/(k*h)-1/h^2≤6*A/h^3) ∧
    (2*h*A≤h^2-k*h ∧ h^2-k*h≤3*h*A) := by sorry

theorem isTheta_of_nonnegative_bounds (f g : ℕ → ℝ) (c C : ℝ) (hc : 0<c)
    (hg : ∀ i,0≤g i) (hlow : ∀ i,c*g i≤f i) (hupp : ∀ i,f i≤C*g i) :
    f =Θ[atTop] g := by sorry

theorem complete_law_support_card {k s : ℕ} (D : CompleteLawData k s) :
    (Concentration.observedAtoms D.law).card=(2^s)^2 := by sorry

theorem complete_law_rate_bounds {k s : ℕ} (D : CompleteLawData k s) (A : ℝ) (ha : 0≤A)
    (hhalf : (2:ℝ)^s/2<(k:ℝ)) (hkh : (k:ℝ)<(2:ℝ)^s)
    (hlow : 2*A≤(2:ℝ)^s-(k:ℝ)) (hupp : (2:ℝ)^s-(k:ℝ)≤3*A) :
    (2*A/(2:ℝ)^s≤1-collision D.law/collision D.optimizer ∧
      1-collision D.law/collision D.optimizer≤3*A/(2:ℝ)^s) ∧
    (2*A/((2:ℝ)^s)^3≤collision D.optimizer-collision D.law ∧
      collision D.optimizer-collision D.law≤6*A/((2:ℝ)^s)^3) ∧
    (2*(2:ℝ)^s*A≤((Concentration.observedAtoms D.law).card:ℝ)-((k*2^s:ℕ):ℝ) ∧
      ((Concentration.observedAtoms D.law).card:ℝ)-((k*2^s:ℕ):ℝ)≤3*(2:ℝ)^s*A) := by sorry

theorem indexed_buffered_laws (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) (hmono : MonotoneOn G (Ici 0))
    (hgap : uniformGapInput G) :
    ∃ S : ℕ,∃ k : ℕ → ℕ,∃ D : (i : ℕ) → CompleteLawData (k i) (S+i),
      ∀ i : ℕ,knownHadamardOrder (k i) ∧
        2*dyadicBuffer G (S+i)≤(2:ℝ)^(S+i)-(k i:ℝ) ∧
        (2:ℝ)^(S+i)-(k i:ℝ)≤3*dyadicBuffer G (S+i) ∧
        3*dyadicBuffer G (S+i)<(2:ℝ)^(S+i)/2 := by sorry

theorem uniform_hadamard_gap_transfer (G : ℝ → ℝ)
    (hG : G =o[atTop] (fun x : ℝ => x))
    (hpos : ∀ x : ℝ,0≤x → 0≤G x) (hmono : MonotoneOn G (Ici 0))
    (hgap : uniformGapInput G) :
    ∃ S : ℕ,∃ k : ℕ → ℕ,∃ D : (i : ℕ) → CompleteLawData (k i) (S+i),
      (∀ i : ℕ,knownHadamardOrder (k i) ∧ knownHadamardOrder (k i*2^(S+i)) ∧
        2*dyadicBuffer G (S+i)≤(2:ℝ)^(S+i)-(k i:ℝ) ∧
        (2:ℝ)^(S+i)-(k i:ℝ)≤3*dyadicBuffer G (S+i)) ∧
      (∀ i : ℕ,(Concentration.observedAtoms (D i).law).card=(2^(S+i))^2 ∧
        collision (D i).law=1/((2:ℝ)^(S+i))^2 ∧
        collision (D i).optimizer=1/((k i*2^(S+i):ℕ):ℝ)) ∧
      Tendsto (fun i => (k i:ℝ)/(2:ℝ)^(S+i)) atTop (nhds 1) ∧
      Tendsto (fun i => collision (D i).law/collision (D i).optimizer) atTop (nhds 1) ∧
      ((fun i => 1-collision (D i).law/collision (D i).optimizer)
        =Θ[atTop] (fun i => dyadicBuffer G (S+i)/(2:ℝ)^(S+i))) ∧
      ((fun i => collision (D i).optimizer-collision (D i).law)
        =Θ[atTop] (fun i => dyadicBuffer G (S+i)/((2:ℝ)^(S+i))^3)) ∧
      ((fun i => ((Concentration.observedAtoms (D i).law).card:ℝ)-((k i*2^(S+i):ℕ):ℝ))
        =Θ[atTop] (fun i => (2:ℝ)^(S+i)*dyadicBuffer G (S+i))) ∧
      (∀ i,∀ q : SourceOutcome (k i) (S+i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k i*2^(S+i))) →
          1-1/(k i:ℝ)≤totalVariation (D i).law q) ∧
      (∀ i,∃ q : SourceOutcome (k i) (S+i) (D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (k i*2^(S+i))) ∧
          totalVariation (D i).law q=1-1/(k i:ℝ)) ∧
      Tendsto (fun i => 1-1/(k i:ℝ)) atTop (nhds 1) := by sorry

end
end EntropyDesigns.GapTransfer

namespace HadamardMultibase
def HadamardOrder (n : ℕ) : Prop :=
  0<n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ,Matrix.IsHadamard H
noncomputable def logScale (n : ℕ) : ℝ := Real.log n/Real.log (Real.log n)
end HadamardMultibase

namespace EntropyDesigns.ArithmeticInterface
theorem uniform_exponent :
    ∃ C : ℝ,0<C ∧ ∃ N : ℕ,∀ x : ℕ,N≤x →
      ∃ T : ℕ,(T:ℝ)≤C*HadamardMultibase.logScale x ∧
        ∀ q : ℕ,Odd q → q≤x → HadamardMultibase.HadamardOrder (2^T*q) := by sorry
end EntropyDesigns.ArithmeticInterface

namespace EntropyDesigns.ProjectInstability
noncomputable section
open Filter Set Asymptotics GapTransfer RelativeSequence SupportFace
open scoped Topology

theorem binary_power_sub_one_odd {d : ℕ} (hd : 0<d) : Odd (2^d-1) := by sorry

theorem buffered_uniform_exponent_law (s S : ℕ) (hS : S<s)
    (hbudget : s≤2^S) (hsmall : 2^S<2^s/2)
    (huniform : ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^S*q)) :
    knownHadamardOrder (2^s-2^S) ∧
    Nonempty (CompleteLawData (2^s-2^S) s) ∧
    2^s-(2^s-2^S)=2^S := by sorry

theorem dyadic_log_scale_ratio_zero :
    Tendsto (fun s : ℕ => (Real.log ((2:ℝ)^s)/Real.log (Real.log ((2:ℝ)^s)))/(s:ℝ))
      atTop (nhds 0) := by sorry

theorem ceiling_log_ratio_zero :
    Tendsto (fun s : ℕ => (Nat.clog 2 s:ℝ)/(s:ℝ)) atTop (nhds 0) := by sorry

theorem ceiling_buffer_budget (s T : ℕ) : s≤2^(max T (Nat.clog 2 s)) := by sorry

def bufferExponent (T : ℕ → ℕ) (s : ℕ) : ℕ := max (T s) (Nat.clog 2 s)

theorem buffer_exponent_ratio_zero (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => (bufferExponent T s:ℝ)/(s:ℝ)) atTop (nhds 0) := by sorry

theorem buffer_exponent_eventually_small (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    ∀ᶠ s : ℕ in atTop,bufferExponent T s+2<s ∧ 2^(bufferExponent T s)<2^s/2 := by sorry

theorem uniform_known_order_lift (T S s : ℕ) (hTS : T≤S)
    (hu : ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^T*q)) :
    ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^S*q) := by sorry

theorem eventually_buffered_uniform_laws (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0))
    (hu : ∀ᶠ s : ℕ in atTop, ∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^(T s)*q)) :
    ∀ᶠ s : ℕ in atTop,
      knownHadamardOrder (2^s-2^(bufferExponent T s)) ∧
      Nonempty (CompleteLawData (2^s-2^(bufferExponent T s)) s) ∧
      2^s-(2^s-2^(bufferExponent T s))=2^(bufferExponent T s) := by sorry

theorem dyadic_power_ratio_eq_exp (S s : ℕ) :
    (2:ℝ)^S/(2:ℝ)^s=Real.exp ((S:ℝ)*Real.log 2-(s:ℝ)*Real.log 2) := by sorry

theorem sublinear_dyadic_gap_ratio_zero (S : ℕ → ℕ)
    (hS : Tendsto (fun s => (S s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => (2:ℝ)^(S s)/(2:ℝ)^s) atTop (nhds 0) := by sorry

theorem sublinear_dyadic_log_ratio_zero (S : ℕ → ℕ)
    (hS : Tendsto (fun s => (S s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => Real.log ((2:ℝ)^(S s))/Real.log ((2:ℝ)^s)) atTop (nhds 0) := by sorry

theorem buffered_order_ratio_one (T : ℕ → ℕ)
    (hT : Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0)) :
    Tendsto (fun s => ((2^s-2^(bufferExponent T s):ℕ):ℝ)/(2:ℝ)^s) atTop (nhds 1) := by sorry

theorem near_square_logarithmic_rates (h k g : ℕ → ℝ)
    (hp : ∀ i,0<h i) (kp : ∀ i,0<k i) (gp : ∀ i,0<g i)
    (hl : Tendsto (fun i => Real.log (h i)) atTop atTop)
    (kr : Tendsto (fun i => k i/h i) atTop (nhds 1))
    (gr : Tendsto (fun i => Real.log (g i)/Real.log (h i)) atTop (nhds 0)) :
    Tendsto (fun i => Real.log (k i*h i)/Real.log (h i)) atTop (nhds 2) ∧
    Tendsto (fun i => Real.log (g i/h i)/Real.log (k i*h i)) atTop (nhds (-(1:ℝ)/2)) ∧
    Tendsto (fun i => Real.log (g i/(k i*(h i)^2)) / Real.log (k i*h i)) atTop (nhds (-(3:ℝ)/2)) ∧
    Tendsto (fun i => Real.log (h i*g i)/Real.log (k i*h i)) atTop (nhds ((1:ℝ)/2)) := by sorry

theorem unconditional_uniform_dyadic_input :
    ∃ T : ℕ → ℕ,Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0) ∧
      ∀ᶠ s : ℕ in atTop,∀ q : ℕ,Odd q → q≤2^s → knownHadamardOrder (2^(T s)*q) := by sorry

theorem unconditional_buffered_laws :
    ∃ T : ℕ → ℕ,Tendsto (fun s => (T s:ℝ)/(s:ℝ)) atTop (nhds 0) ∧
      Tendsto (fun s => ((2^s-2^(bufferExponent T s):ℕ):ℝ)/(2:ℝ)^s) atTop (nhds 1) ∧
      Tendsto (fun s => Real.log ((2:ℝ)^(bufferExponent T s))/Real.log ((2:ℝ)^s)) atTop (nhds 0) ∧
      ∀ᶠ s : ℕ in atTop,
        knownHadamardOrder (2^s-2^(bufferExponent T s)) ∧
        Nonempty (CompleteLawData (2^s-2^(bufferExponent T s)) s) ∧
        2^s-(2^s-2^(bufferExponent T s))=2^(bufferExponent T s) := by sorry

theorem normalized_inverse_order_ratio_one (h k : ℕ → ℝ)
    (hp : ∀ i,0<h i) (kp : ∀ i,0<k i)
    (hr : Tendsto (fun i => k i/h i) atTop (nhds 1)) :
    Tendsto (fun i => Real.sqrt (k i*h i)/k i) atTop (nhds 1) := by sorry

theorem reciprocal_entropy_ratio_one (r : ℕ → ℝ)
    (hp : ∀ i,0<r i) (hlt : ∀ i,r i<1)
    (hr : Tendsto r atTop (nhds 1)) :
    Tendsto (fun i => -Real.log (r i)/(1-r i)) atTop (nhds 1) := by sorry

theorem logarithmic_rate_of_ratio_one (f b n : ℕ → ℝ) (c : ℝ)
    (hf : ∀ i,0<f i) (hb : ∀ i,0<b i)
    (hn : Tendsto (fun i => Real.log (n i)) atTop atTop)
    (hr : Tendsto (fun i => f i/b i) atTop (nhds 1))
    (hc : Tendsto (fun i => Real.log (b i)/Real.log (n i)) atTop (nhds c)) :
    Tendsto (fun i => Real.log (f i)/Real.log (n i)) atTop (nhds c) := by sorry

structure DyadicLawFamily where
  T : ℕ → ℕ
  base : ℕ
  D : (i : ℕ) → CompleteLawData (2^(base+i)-2^(bufferExponent T (base+i))) (base+i)
  known : ∀ i,knownHadamardOrder (2^(base+i)-2^(bufferExponent T (base+i)))
  small : ∀ i,bufferExponent T (base+i)+2<base+i ∧
    2^(bufferExponent T (base+i))<2^(base+i)/2
  ratio : Tendsto (fun i => ((2^(base+i)-2^(bufferExponent T (base+i)):ℕ):ℝ)/(2:ℝ)^(base+i)) atTop (nhds 1)
  loggap : Tendsto (fun i => Real.log ((2:ℝ)^(bufferExponent T (base+i)))/Real.log ((2:ℝ)^(base+i))) atTop (nhds 0)

def DyadicLawFamily.seedOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := 2^(F.base+i)
def DyadicLawFamily.gapOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := 2^(bufferExponent F.T (F.base+i))
def DyadicLawFamily.lowOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := F.seedOrder i-F.gapOrder i

theorem dyadic_law_family_exists : Nonempty DyadicLawFamily := by sorry

theorem dyadic_family_orders (F : DyadicLawFamily) (i : ℕ) :
    0<F.lowOrder i ∧ F.lowOrder i<F.seedOrder i ∧
    0<F.gapOrder i ∧ F.seedOrder i-F.lowOrder i=F.gapOrder i ∧
    F.seedOrder i<2*F.lowOrder i := by sorry

theorem dyadic_family_cast_identity (F : DyadicLawFamily) (i : ℕ) :
    (F.lowOrder i:ℝ)=(F.seedOrder i:ℝ)-(F.gapOrder i:ℝ) := by sorry

def DyadicLawFamily.fullOrder (F : DyadicLawFamily) (i : ℕ) : ℕ := F.lowOrder i*F.seedOrder i

theorem dyadic_family_numeric_rates (F : DyadicLawFamily) :
    Tendsto (fun i => Real.log ((F.fullOrder i:ℝ))) atTop atTop ∧
    Tendsto (fun i => Real.log ((F.gapOrder i:ℝ)/(F.seedOrder i:ℝ))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) ∧
    Tendsto (fun i => Real.log ((F.gapOrder i:ℝ)/((F.lowOrder i:ℝ)*(F.seedOrder i:ℝ)^2))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(3:ℝ)/2)) ∧
    Tendsto (fun i => Real.log ((F.seedOrder i:ℝ)*(F.gapOrder i:ℝ))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds ((1:ℝ)/2)) ∧
    Tendsto (fun i => Real.sqrt ((F.fullOrder i:ℝ))/(F.lowOrder i:ℝ)) atTop (nhds 1) ∧
    Tendsto (fun i => Real.log (Real.log ((F.seedOrder i:ℝ)/(F.lowOrder i:ℝ)))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) := by sorry

theorem dyadic_family_law_identities (F : DyadicLawFamily) (i : ℕ) :
    knownHadamardOrder (F.lowOrder i) ∧ knownHadamardOrder (F.fullOrder i) ∧
    (Concentration.observedAtoms (F.D i).law).card=(F.seedOrder i)^2 ∧
    collision (F.D i).law=1/(F.seedOrder i:ℝ)^2 ∧
    collision (F.D i).optimizer=1/(F.fullOrder i:ℝ) ∧
    1-collision (F.D i).law/collision (F.D i).optimizer=(F.gapOrder i:ℝ)/(F.seedOrder i:ℝ) ∧
    collision (F.D i).optimizer-collision (F.D i).law=
      (F.gapOrder i:ℝ)/((F.lowOrder i:ℝ)*(F.seedOrder i:ℝ)^2) ∧
    ((Concentration.observedAtoms (F.D i).law).card:ℝ)-(F.fullOrder i:ℝ)=
      (F.seedOrder i:ℝ)*(F.gapOrder i:ℝ) ∧
    (∀ α : ℝ,0<α → renyiEntropy (F.D i).law α-renyiEntropy (F.D i).optimizer α=
      Real.log ((F.seedOrder i:ℝ)/(F.lowOrder i:ℝ))) ∧
    minEntropy (F.D i).law-minEntropy (F.D i).optimizer=
      Real.log ((F.seedOrder i:ℝ)/(F.lowOrder i:ℝ)) := by sorry

theorem unconditional_near_square_instability :
    ∃ F : DyadicLawFamily,
      (∀ i,knownHadamardOrder (F.lowOrder i) ∧ knownHadamardOrder (F.fullOrder i) ∧
        (Concentration.observedAtoms (F.D i).law).card=(F.seedOrder i)^2 ∧
        collision (F.D i).law=1/(F.seedOrder i:ℝ)^2 ∧
        collision (F.D i).optimizer=1/(F.fullOrder i:ℝ)) ∧
      Tendsto (fun i => (F.fullOrder i:ℝ)) atTop atTop ∧
      Tendsto (fun i => collision (F.D i).law/collision (F.D i).optimizer) atTop (nhds 1) ∧
      Tendsto (fun i => Real.log (1-collision (F.D i).law/collision (F.D i).optimizer)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) ∧
      Tendsto (fun i => Real.log (collision (F.D i).optimizer-collision (F.D i).law)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(3:ℝ)/2)) ∧
      Tendsto (fun i => Real.log (((Concentration.observedAtoms (F.D i).law).card:ℝ)-(F.fullOrder i:ℝ))/Real.log ((F.fullOrder i:ℝ))) atTop (nhds ((1:ℝ)/2)) ∧
      (∀ α : ℝ,0<α → Tendsto (fun i => Real.log (renyiEntropy (F.D i).law α-renyiEntropy (F.D i).optimizer α)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2))) ∧
      Tendsto (fun i => Real.log (minEntropy (F.D i).law-minEntropy (F.D i).optimizer)/Real.log ((F.fullOrder i:ℝ))) atTop (nhds (-(1:ℝ)/2)) ∧
      Tendsto (fun i => Real.sqrt ((F.fullOrder i:ℝ))/(F.lowOrder i:ℝ)) atTop (nhds 1) ∧
      Tendsto (fun i => 1-1/(F.lowOrder i:ℝ)) atTop (nhds 1) ∧
      (∀ i,∀ q : SourceOutcome (F.lowOrder i) (F.base+i) (F.D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (F.fullOrder i)) →
          1-1/(F.lowOrder i:ℝ)≤totalVariation (F.D i).law q) ∧
      (∀ i,∃ q : SourceOutcome (F.lowOrder i) (F.base+i) (F.D i).i0 → ℝ,
        q∈convexHull ℝ (SupportWitness.blockLaws observedOrthogonal (F.fullOrder i)) ∧
          totalVariation (F.D i).law q=1-1/(F.lowOrder i:ℝ)) := by sorry

end
end EntropyDesigns.ProjectInstability
