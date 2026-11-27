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
