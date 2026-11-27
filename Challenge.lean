module
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Logic.Relation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Lattice.Lemmas
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
/-! Independent mathlib-only specification. Intentional proof placeholders occur only here. -/
@[expose] public section
open Filter
open scoped Topology
namespace EntropyDesigns
open scoped symmDiff
def inner {α ι : Type*} [Fintype ι] (v : α → ι → ℝ) (a b : α) : ℝ :=
  ∑ i, v a i * v b i
def collision {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  ∑ a, w a ^ 2
def weightedTotal {α : Type*} [Fintype α] (w : α → ℝ) (P : α → α → ℝ) : ℝ :=
  ∑ a, ∑ b, w a * w b * P a b
def projectionCoefficients {α ι : Type*} [Fintype α]
    (w ε : α → ℝ) (v : α → ι → ℝ) : ι → ℝ :=
  fun i => ∑ a, w a * ε a * v a i
def intInner {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a b : α) : ℤ :=
  ∑ i, A a i * A b i
def intParity {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a : α) : ℤ :=
  ∏ i, A a i
def roundedDimension (n : ℕ) : ℕ := 4 * ((n + 3) / 4)
noncomputable def shannon {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -(∑ a, w a * Real.log (w a))
noncomputable def collisionEntropy {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  -Real.log (collision w)
def augmentedSign {α : Type*} {d : ℕ} (x : α → Fin d → ℤ) (a : α) :
    Fin (d + 1) → ℤ := Fin.cases 1 (x a)
def bitSign (b : Bool) : ℤ := if b then -1 else 1
def pushLaw {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (w : α → ℝ) (b : β) : ℝ :=
  ∑ a, if f a = b then w a else 0
def offDiagonalTotal {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else w a * w b * P a b
def residueKernel {α : Type*} {n : ℕ} (A : α → Fin n → ℤ) (a b : α) : ℝ :=
  (intInner A a b : ℝ) ^ 2 +
    2 * ((intParity A a : ℝ) * (intParity A b : ℝ) * (intInner A a b : ℝ)) - 3
def parityResidual {α : Type*} [Fintype α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ) (a : α) : ℝ :=
  (intParity A a : ℝ) -
    ∑ i, projectionCoefficients w (fun a => (intParity A a : ℝ))
      (fun a i => (A a i : ℝ)) i * (A a i : ℝ)
def offDiagonalRow {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (P : α → α → ℝ) (a : α) : ℝ :=
  ∑ b, if a = b then 0 else w b * P a b
def badPairMass {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ) : ℝ :=
  offDiagonalTotal w (fun a b =>
    if intParity A a * intParity A b * intInner A a b = -3 ∨
      intParity A a * intParity A b * intInner A a b = 1 then 0 else 1)
noncomputable def uniformOn {α : Type*} [DecidableEq α] (G : Finset α) (N : ℕ) (a : α) : ℝ :=
  if a ∈ G then 1 / (N : ℝ) else 0
noncomputable def goodSupport {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (N : ℕ) : Finset α := by
  classical
  exact Finset.univ.filter (fun a =>
    |(N : ℝ) * w a - 1| ≤ 1 / (4 * (N : ℝ)))
def walshChar {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) : ℤ :=
  ∏ i ∈ S, bitSign (x i)
def flipCoordinate {d : ℕ} (j : Fin d) : (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun x := Function.update x j (!x j)
  invFun x := Function.update x j (!x j)
  left_inv x := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [Function.update_of_ne h]
  right_inv x := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [Function.update_of_ne h]
abbrev LowIndex (d : ℕ) := {S : Finset (Fin d) // S.Nonempty ∧ S.card ≤ 2}
def lowCharacter {d : ℕ} (i : LowIndex d) (x : Fin d → Bool) : ℝ :=
  (walshChar i.val x : ℝ)
noncomputable def affineCorrection {α : Type*}
    (w f : α → ℝ) (M B : ℝ) (a : α) : ℝ :=
  (w a + (B - f a) / M) / (1 + B)
def fourierPolynomial {α σ : Type*} [Fintype σ]
    (m : σ → ℝ) (φ : σ → α → ℝ) (a : α) : ℝ :=
  ∑ i, m i * φ i a
def fourierCoefficient {α σ : Type*} [Fintype α]
    (w : α → ℝ) (φ : σ → α → ℝ) (i : σ) : ℝ :=
  ∑ a, w a * φ i a
def lowPolynomial {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) : ℝ :=
  fourierPolynomial (fourierCoefficient w lowCharacter) lowCharacter x
noncomputable def correctionBuffer {d : ℕ} (w : (Fin d → Bool) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (lowPolynomial w)
noncomputable def coefficientBudget {d : ℕ} (w : (Fin d → Bool) → ℝ) : ℝ :=
  ∑ i : LowIndex d, |fourierCoefficient w lowCharacter i|
noncomputable def correctedLaw {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) : ℝ :=
  affineCorrection w (lowPolynomial w) ((2 : ℝ) ^ d) (correctionBuffer w) x
def probabilityBlend {α : Type*} (p q : α → ℝ) (t : ℝ) (a : α) : ℝ :=
  (1 - t) * p a + t * q a
def lawOverlap {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * q a
noncomputable def bridgeTime (a b c : ℝ) : ℝ :=
  max (a - c) 0 / (a + b - 2 * c)
noncomputable def bridgeLoss (a b c : ℝ) : ℝ :=
  (max (a - c) 0) ^ 2 / (a + b - 2 * c)
noncomputable def supportRightInverse {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) : Matrix α ι ℝ :=
  A.transpose * (A * A.transpose)⁻¹
noncomputable def supportCorrection {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) : α → ℝ :=
  p - (supportRightInverse A).mulVec (A.mulVec p - b)
noncomputable def supportCondition {ι α : Type*} [Fintype ι] [Fintype α]
    [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a => ∑ i, |supportRightInverse A a i|)
def maskSeed {d : ℕ} (S : Finset (Fin d)) (i : Fin d) : Bool := decide (i ∈ S)
def seedMask {d : ℕ} (x : Fin d → Bool) : Finset (Fin d) :=
  Finset.univ.filter (fun i => x i = true)
def maskSeedEquiv (d : ℕ) : Finset (Fin d) ≃ (Fin d → Bool) where
  toFun := maskSeed
  invFun := seedMask
  left_inv S := by
    ext i
    simp [maskSeed, seedMask]
  right_inv x := by
    funext i
    cases h : x i <;> simp [maskSeed, seedMask, h]
def walshCoefficient {d : ℕ} (w : (Fin d → Bool) → ℝ) (S : Finset (Fin d)) : ℝ :=
  ∑ x, w x * (walshChar S x : ℝ)
def maskSumset {d : ℕ} (A : Finset (Finset (Fin d))) : Finset (Finset (Fin d)) :=
  A.biUnion (fun S => A.image (fun T => S ∆ T))
def maskTranslate {d : ℕ} (c : Finset (Fin d)) : Finset (Fin d) ≃ Finset (Fin d) where
  toFun S := S ∆ c
  invFun S := S ∆ c
  left_inv S := by simp
  right_inv S := by simp
noncomputable def characterTilt {d : ℕ} (c : Finset (Fin d)) (t : ℝ)
    (x : Fin d → Bool) : ℝ := (1 + t * (walshChar c x : ℝ)) / (2 : ℝ) ^ d
def characterLevel {d : ℕ} (c : Finset (Fin d)) (e : ℤ) : Finset (Fin d → Bool) :=
  Finset.univ.filter (fun x => walshChar c x = e)
def binarySeed {d : ℕ} (x : Fin d → Bool) : Fin d → ZMod 2 :=
  fun i => if x i then 1 else 0
def maskFunctional {d : ℕ} (c : Finset (Fin d)) : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun z := ∑ i ∈ c, z i
  map_add' z w := by simp [Finset.sum_add_distrib]
  map_smul' a z := by simp [Finset.mul_sum]
def seedDotFunctional {d : ℕ} (z : Fin d → ZMod 2) : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun a := ∑ i, a i * z i
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, mul_assoc]
def characterCode {d : ℕ} (B : Finset (Finset (Fin d))) (x : Fin d → Bool) : B → Bool :=
  fun S => decide (walshChar S.val x = -1)
def trapMixed {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool)) : ℤ :=
  walshChar e u.1 * walshChar e u.2
def trapRow {s : ℕ} (e : Finset (Fin s)) (u : (Fin s → Bool) × (Fin s → Bool)) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → ℤ :=
  Sum.elim (fun S => walshChar S u.1)
    (fun S => if S = ∅ then trapMixed e u else walshChar S u.2)
def trapInner {s : ℕ} (e : Finset (Fin s)) (u v : (Fin s → Bool) × (Fin s → Bool)) : ℤ :=
  ∑ j, trapRow e u j * trapRow e v j
def trapOrthogonal {s : ℕ} (e : Finset (Fin s))
    (S : Finset ((Fin s → Bool) × (Fin s → Bool))) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → trapInner e u v = 0
def walshSquare {s : ℕ} : Matrix (Finset (Fin s)) (Finset (Fin s)) ℝ :=
  fun R S => (walshChar S (maskSeed R) : ℝ)
def permutedWalsh {s : ℕ} (π : (Fin s → Bool) ≃ (Fin s → Bool)) (c : ℤ) :
    Matrix (Finset (Fin s)) (Finset (Fin s)) ℝ :=
  fun R S => if S = ∅ then (c : ℝ) else (walshChar S (π (maskSeed R)) : ℝ)
noncomputable def trapRowIndices {s : ℕ} (e : Finset (Fin s))
    (H : Matrix (Finset (Fin s) ⊕ Finset (Fin s)) (Finset (Fin s) ⊕ Finset (Fin s)) ℝ) :
    Finset (Finset (Fin s) ⊕ Finset (Fin s)) := by
  classical
  exact Finset.univ.filter (fun i => ∃ u : (Fin s → Bool) × (Fin s → Bool),
    ∀ j, H i j = (trapRow e u j : ℝ))
def trapMask {s : ℕ} (e : Finset (Fin s)) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s) :=
  Sum.elim (fun S => (S, ∅)) (fun S => if S = ∅ then (e, e) else (∅, S))
abbrev TrapCoordinate (s : ℕ) :=
  {j : Finset (Fin s) ⊕ Finset (Fin s) // j ≠ Sum.inl ∅}
def trapCode {s : ℕ} (e : Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) : TrapCoordinate s → Bool :=
  fun j => decide (trapRow e u j.val = -1)
noncomputable def trapSeedWeight {s : ℕ} (_ : (Fin s → Bool) × (Fin s → Bool)) : ℝ :=
  1 / (Fintype.card ((Fin s → Bool) × (Fin s → Bool)) : ℝ)
noncomputable def trapLaw {s : ℕ} (e : Finset (Fin s)) : (TrapCoordinate s → Bool) → ℝ := by
  classical
  exact pushLaw (trapCode e) trapSeedWeight
def endpointRow {s : ℕ} (u : (Fin s → Bool) × Bool) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → ℤ :=
  Sum.elim (fun S => walshChar S u.1) (fun S => bitSign u.2 * walshChar S u.1)
def endpointCode {s : ℕ} (u : (Fin s → Bool) × Bool) : TrapCoordinate s → Bool :=
  fun j => decide (endpointRow u j.val = -1)
noncomputable def endpointSeedWeight {s : ℕ} (_ : (Fin s → Bool) × Bool) : ℝ :=
  1 / (Fintype.card ((Fin s → Bool) × Bool) : ℝ)
noncomputable def endpointLaw (s : ℕ) : (TrapCoordinate s → Bool) → ℝ := by
  classical
  exact pushLaw endpointCode endpointSeedWeight
def observedFrame {s : ℕ} (x : TrapCoordinate s → Bool)
    (j : Finset (Fin s) ⊕ Finset (Fin s)) : ℝ :=
  if h : j = Sum.inl ∅ then 1 else (bitSign (x ⟨j, h⟩) : ℝ)
def observedFeasible {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ) : Prop :=
  (∀ x, 0 ≤ w x) ∧ (∑ x, w x) = 1 ∧
    (∀ j, ∑ x, w x * (bitSign (x j) : ℝ) = 0) ∧
    (∀ i j, i ≠ j → ∑ x, w x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ) = 0)
noncomputable def commonTrapSeeds {s : ℕ} (e : Finset (Fin s))
    (w : (TrapCoordinate s → Bool) → ℝ) : Finset ((Fin s → Bool) × (Fin s → Bool)) := by
  classical
  exact Finset.univ.filter (fun u => w (trapCode e u) ≠ 0)
noncomputable def linearSeedWeight {V : Type*} [Fintype V] (_ : V) : ℝ :=
  1 / (Fintype.card V : ℝ)
noncomputable def linearLaw {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W]
    (L : V →ₗ[ZMod 2] W) : W → ℝ := by
  classical
  exact pushLaw L linearSeedWeight
def rewireMask {s : ℕ} (e : Finset (Fin s)) (T : Finset (Finset (Fin s))) :
    (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s) :=
  Sum.elim (fun S => (S, ∅))
    (fun S => if S = ∅ then (∅, e) else if S = e ∨ S ∈ T then (S, e) else (∅, S))
def initialSwapIndex {s : ℕ} (e : Finset (Fin s)) :
    (Finset (Fin s) ⊕ Finset (Fin s)) ≃ (Finset (Fin s) ⊕ Finset (Fin s)) :=
  Equiv.swap (Sum.inr ∅) (Sum.inr e)
def maskPairRow {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) (j : Finset (Fin s) ⊕ Finset (Fin s)) : ℤ :=
  walshChar (M j).1 u.1 * walshChar (M j).2 u.2
def maskPairCode {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s))
    (u : (Fin s → Bool) × (Fin s → Bool)) : TrapCoordinate s → Bool :=
  fun j => decide (maskPairRow M u j.val = -1)
noncomputable def maskPairLaw {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    (TrapCoordinate s → Bool) → ℝ := by
  classical
  exact pushLaw (maskPairCode M) trapSeedWeight
noncomputable def rewireLaw {s : ℕ} (e : Finset (Fin s)) (T : Finset (Finset (Fin s))) :
    (TrapCoordinate s → Bool) → ℝ := maskPairLaw (rewireMask e T)
noncomputable def rewiringList {s : ℕ} (e : Finset (Fin s)) : List (Finset (Fin s)) :=
  ((Finset.univ.erase ∅).erase e).toList
noncomputable def rewiringPrefix {s : ℕ} (e : Finset (Fin s)) (k : ℕ) : Finset (Finset (Fin s)) :=
  ((rewiringList e).take k).toFinset
noncomputable def rewiringScheduleLaw {s : ℕ} (e : Finset (Fin s)) (k : ℕ) :
    (TrapCoordinate s → Bool) → ℝ := rewireLaw e (rewiringPrefix e k)
def fieldCode {ι : Type*} (z : ι → ZMod 2) : ι → Bool := fun i => decide (z i = 1)
def pairedBinarySeed {s : ℕ} (u : (Fin s → Bool) × (Fin s → Bool)) :
    (Fin s → ZMod 2) × (Fin s → ZMod 2) := (binarySeed u.1, binarySeed u.2)
def maskPairLinear {s : ℕ}
    (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) :
    ((Fin s → ZMod 2) × (Fin s → ZMod 2)) →ₗ[ZMod 2] (TrapCoordinate s → ZMod 2) where
  toFun z j := maskFunctional (M j.val).1 z.1 + maskFunctional (M j.val).2 z.2
  map_add' x y := by
    funext j
    change maskFunctional (M j.val).1 (x.1 + y.1) + maskFunctional (M j.val).2 (x.2 + y.2) = _
    rw [map_add, map_add]
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext j
    change maskFunctional (M j.val).1 (a • x.1) + maskFunctional (M j.val).2 (a • x.2) = _
    simp [map_smul, mul_add]
def rankOneRepair {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (v : W) (f : W →ₗ[ZMod 2] ZMod 2) : W →ₗ[ZMod 2] W := LinearMap.id - f.smulRight v
def rightCoordinate {s : ℕ} (b : Finset (Fin s)) : TrapCoordinate s := ⟨Sum.inr b, by simp⟩
def leftCoordinate {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) : TrapCoordinate s :=
  ⟨Sum.inl b, by simpa using hb⟩
def rewireDefect {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) :
    (TrapCoordinate s → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (R := ZMod 2) (φ := fun _ : TrapCoordinate s => ZMod 2) (rightCoordinate b) -
    LinearMap.proj (R := ZMod 2) (φ := fun _ : TrapCoordinate s => ZMod 2) (leftCoordinate b hb) -
    LinearMap.proj (R := ZMod 2) (φ := fun _ : TrapCoordinate s => ZMod 2) (rightCoordinate ∅)
def rewireRepair {s : ℕ} (b : Finset (Fin s)) (hb : b ≠ ∅) :
    (TrapCoordinate s → ZMod 2) →ₗ[ZMod 2] (TrapCoordinate s → ZMod 2) :=
  rankOneRepair (Pi.single (rightCoordinate b) 1) (rewireDefect b hb)
noncomputable def rewiringRank {s : ℕ} (e : Finset (Fin s)) (k : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear (rewireMask e (rewiringPrefix e k))))
def differenceEncoder {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module (ZMod 2) V] [Module (ZMod 2) W] (L M : V →ₗ[ZMod 2] W) :
    (V × V) →ₗ[ZMod 2] W := L.coprod (-M)
noncomputable def rewiringPath {s : ℕ} (e : Finset (Fin s))
    (j : Fin ((rewiringList e).length + 1)) (t : ℝ) : (TrapCoordinate s → Bool) → ℝ :=
  Fin.cases (probabilityBlend (trapLaw e) (rewireLaw e ∅) t)
    (fun k => probabilityBlend (rewiringScheduleLaw e k.val) (rewiringScheduleLaw e (k.val + 1)) t) j
noncomputable def activeSupport {α : Type*} [Fintype α] (p : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => p a ≠ 0)
def feasibleLaw {ι α : Type*} [Fintype α] (A : Matrix ι α ℝ)
    (b : ι → ℝ) (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧ A.mulVec p = b
noncomputable def realLaw {α : Type*} (p : α → ℚ) : α → ℝ := fun a => (p a : ℝ)
theorem sign_sum_mod_four {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) : (∑ i ∈ s, f i) % 4 = ((s.card : ℤ) - 1 + ∏ i ∈ s, f i) % 4 := by sorry
theorem odd_sign_sum_square_ge_one {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hn : s.card % 2 = 1) : 1 ≤ (∑ i ∈ s, f i) ^ 2 := by sorry
theorem switched_sign_sum_mod_four {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hn : s.card % 4 = 1) : ((∏ i ∈ s, f i) * (∑ i ∈ s, f i)) % 4 = 1 := by sorry
theorem residue_one_polynomial_nonneg (q : ℤ) (hq : q % 4 = 1) : 0 ≤ q ^ 2 + 2 * q - 3 := by sorry
theorem residue_two_sign_square_lower {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, f i = 1 ∨ f i = -1) (hn : s.card % 4 = 2) : 2 + 2 * (∏ i ∈ s, f i) ≤ (∑ i ∈ s, f i) ^ 2 := by sorry
theorem odd_dimension_collision_arithmetic {n C : ℝ} (hn : 1 < n) (hbound : C * (n ^ 2 - 1) ≤ n - 1) : C ≤ 1 / (n + 1) := by sorry
theorem residue_two_collision_arithmetic {n C : ℝ} (hn : 2 < n) (hbound : C * (n ^ 2 - 4) ≤ n - 2) : C ≤ 1 / (n + 2) := by sorry
theorem residue_one_collision_arithmetic {n C : ℝ} (hn : 1 < n) (hbound : C * (n ^ 2 + 2 * n - 3) ≤ n - 1) : C ≤ 1 / (n + 3) := by sorry
theorem shannon_ge_collision_entropy {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) : collisionEntropy w ≤ shannon w := by sorry
theorem sharp_sign_cube_entropy_bounds {d : ℕ} (hd : 2 ≤ d) (w : (Fin d → Bool) → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hmean : ∀ i, ∑ a, w a * (bitSign (a i) : ℝ) = 0) (hpair : ∀ i j, i ≠ j → ∑ a, w a * (bitSign (a i) : ℝ) * (bitSign (a j) : ℝ) = 0) : collision w ≤ 1 / (roundedDimension (d + 1) : ℝ) ∧ Real.log (roundedDimension (d + 1)) ≤ collisionEntropy w ∧ Real.log (roundedDimension (d + 1)) ≤ shannon w := by sorry
theorem odd_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (heq : collision w = 1 / ((n : ℝ) + 1)) : ∀ a, w a = 0 ∨ w a = 1 / ((n : ℝ) + 1) := by sorry
theorem residue_two_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 2 < n) (hres : n % 4 = 2) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (heq : collision w = 1 / ((n : ℝ) + 2)) : ∀ a, w a = 0 ∨ w a = 1 / ((n : ℝ) + 2) := by sorry
theorem residue_one_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (heq : collision w = 1 / ((n : ℝ) + 3)) : ∀ a, w a = 0 ∨ w a = 1 / ((n : ℝ) + 3) := by sorry
theorem sharp_frame_equality_uniform {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (heq : collision w = 1 / (roundedDimension n : ℝ)) : ∀ a, w a = 0 ∨ w a = 1 / (roundedDimension n : ℝ) := by sorry
theorem sharp_frame_equality_support_card {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (heq : collision w = 1 / (roundedDimension n : ℝ)) : (Finset.univ.filter (fun a => w a ≠ 0)).card = roundedDimension n := by sorry
theorem sharp_frame_entropy_equality_iff {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) : shannon w = Real.log (roundedDimension n) ↔ collision w = 1 / (roundedDimension n : ℝ) := by sorry
theorem sharp_frame_equality_support_gram {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 3 ≤ n) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (heq : collision w = 1 / (roundedDimension n : ℝ)) (i j : Fin n) : (∑ a ∈ Finset.univ.filter (fun a => w a ≠ 0), (A a i : ℝ) * (A a j : ℝ)) = if i = j then (roundedDimension n : ℝ) else 0 := by sorry
theorem pushLaw_nonneg {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) : ∀ b, 0 ≤ pushLaw f w b := by sorry
theorem pushLaw_mass {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) (w : α → ℝ) : (∑ b, pushLaw f w b) = ∑ a, w a := by sorry
theorem pushLaw_moment {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) (w : α → ℝ) (g : β → ℝ) : (∑ b, pushLaw f w b * g b) = ∑ a, w a * g (f a) := by sorry
theorem cube_law_of_hadamard {d : ℕ} (hd : 2 ≤ d) (H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ) (hH : Matrix.IsHadamard H) : ∃ w : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧ (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧ (∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧ collision w = 1 / (roundedDimension (d + 1) : ℝ) ∧ collisionEntropy w = Real.log (roundedDimension (d + 1)) ∧ shannon w = Real.log (roundedDimension (d + 1)) := by sorry
theorem sharp_sign_cube_equality_completion {d : ℕ} (hd : 2 ≤ d) (w : (Fin d → Bool) → ℝ) (hw : ∀ b, 0 ≤ w b) (hmass : ∑ b, w b = 1) (hmean : ∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) (hpair : ∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) (heq : collision w = 1 / (roundedDimension (d + 1) : ℝ)) : (∀ b, w b = 0 ∨ w b = 1 / (roundedDimension (d + 1) : ℝ)) ∧ (Finset.univ.filter (fun b => w b ≠ 0)).card = roundedDimension (d + 1) ∧ ∃ (H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ) (columns : Fin (d + 1) ↪ Fin (roundedDimension (d + 1))) (rows : {b // w b ≠ 0} ≃ Fin (roundedDimension (d + 1))), Matrix.IsHadamard H ∧ ∀ b i, H (rows b) (columns i) = (augmentedSign (fun (b : Fin d → Bool) i => bitSign (b i)) (b : Fin d → Bool) i : ℝ) := by sorry
theorem collision_entropy_equality_iff {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) {N : ℝ} (hN : 0 < N) : collisionEntropy w = Real.log N ↔ collision w = 1 / N := by sorry
theorem collision_attainment_iff_hadamard {d : ℕ} (hd : 2 ≤ d) : (∃ w : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧ (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧ (∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧ collision w = 1 / (roundedDimension (d + 1) : ℝ)) ↔ ∃ H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ, Matrix.IsHadamard H := by sorry
theorem entropy_attainment_iff_hadamard {d : ℕ} (hd : 2 ≤ d) : (∃ w : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ (∑ b, w b = 1) ∧ (∀ i, ∑ b, w b * (bitSign (b i) : ℝ) = 0) ∧ (∀ i j, i ≠ j → ∑ b, w b * (bitSign (b i) : ℝ) * (bitSign (b j) : ℝ) = 0) ∧ (collisionEntropy w = Real.log (roundedDimension (d + 1)) ∨ shannon w = Real.log (roundedDimension (d + 1)))) ↔ ∃ H : Matrix (Fin (roundedDimension (d + 1))) (Fin (roundedDimension (d + 1))) ℝ, Matrix.IsHadamard H := by sorry
theorem offDiagonalTotal_identity {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ) (P : α → α → ℝ) (D : ℝ) (hdiag : ∀ a, P a a = D) : offDiagonalTotal w P = weightedTotal w P - collision w * D := by sorry
theorem offDiagonalTotal_nonneg {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ) (P : α → α → ℝ) (hw : ∀ a, 0 ≤ w a) (hP : ∀ a b, 0 ≤ P a b) : 0 ≤ offDiagonalTotal w P := by sorry
theorem residue_one_polynomial_gap (q : ℤ) (hq : q % 4 = 1) (h₁ : q ≠ -3) (h₂ : q ≠ 1) : 32 ≤ q ^ 2 + 2 * q - 3 := by sorry
theorem residue_frame_defect_decomposition {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) : (((n : ℝ) ^ 2 + 2 * n - 3) * (1 / ((n : ℝ) + 3) - collision w) = 2 * (∑ a, w a * parityResidual A w a ^ 2) + offDiagonalTotal w (residueKernel A)) ∧ 0 ≤ (∑ a, w a * parityResidual A w a ^ 2) ∧ 0 ≤ offDiagonalTotal w (residueKernel A) := by sorry
theorem weighted_abs_le_sqrt_second_moment {α : Type*} [Fintype α] (w h : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) : (∑ a, w a * |h a|) ≤ Real.sqrt (∑ a, w a * h a ^ 2) := by sorry
theorem offDiagonalRow_identity {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ) (P : α → α → ℝ) (a : α) : offDiagonalRow w P a = (∑ b, w b * P a b) - w a * P a a := by sorry
theorem offDiagonalRow_nonneg {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ) (P : α → α → ℝ) (hw : ∀ a, 0 ≤ w a) (hP : ∀ a b, 0 ≤ P a b) (a : α) : 0 ≤ offDiagonalRow w P a := by sorry
theorem twisted_intInner_mod_four {α : Type*} {n : ℕ} (hres : n % 4 = 1) (A : α → Fin n → ℤ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (a b : α) : (intParity A a * intParity A b * intInner A a b) % 4 = 1 := by sorry
theorem residue_frame_weight_deviation {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) : (∑ a, w a * |w a - 1 / ((n : ℝ) + 3)|) ≤ Real.sqrt (2 * (1 / ((n : ℝ) + 3) - collision w) / ((n : ℝ) ^ 2 + 2 * n - 3)) + (1 / ((n : ℝ) + 3) - collision w) := by sorry
theorem offDiagonalTotal_smul {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℝ) (P : α → α → ℝ) (c : ℝ) : offDiagonalTotal w (fun a b => c * P a b) = c * offDiagonalTotal w P := by sorry
theorem residue_frame_bad_pair_mass {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) : badPairMass A w ≤ ((n : ℝ) ^ 2 + 2 * n - 3) * (1 / ((n : ℝ) + 3) - collision w) / 32 := by sorry
theorem residue_frame_deficit_nonneg {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 1 < n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) : 0 ≤ 1 / ((n : ℝ) + 3) - collision w := by sorry
theorem small_deficit_exact_extraction {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (hsmall : 1 / ((n : ℝ) + 3) - collision w ≤ 1 / (1024 * ((n : ℝ) + 3) ^ 4)) : (goodSupport w (n + 3)).card = n + 3 ∧ (∀ i j, ∑ a, uniformOn (goodSupport w (n + 3)) (n + 3) a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) ∧ ∃ H : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ, Matrix.IsHadamard H := by sorry
theorem no_hadamard_forces_strict_collision_gap {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (hno : ¬∃ H : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ, Matrix.IsHadamard H) : collision w < 1 / ((n : ℝ) + 3) - 1 / (1024 * ((n : ℝ) + 3) ^ 4) := by sorry
theorem small_deficit_preserving_reconstruction {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 5 ≤ n) (hres : n % 4 = 1) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) (hsmall : 1 / ((n : ℝ) + 3) - collision w ≤ 1 / (1024 * ((n : ℝ) + 3) ^ 4)) : roundedDimension n = n + 3 ∧ ∃ (H : Matrix (Fin (roundedDimension n)) (Fin (roundedDimension n)) ℝ) (columns : Fin n ↪ Fin (roundedDimension n)) (rows : {a // uniformOn (goodSupport w (n + 3)) (n + 3) a ≠ 0} ≃ Fin (roundedDimension n)), Matrix.IsHadamard H ∧ ∀ a i, H (rows a) (columns i) = (A a i : ℝ) := by sorry
theorem correctionBuffer_nonneg {d : ℕ} (w : (Fin d → Bool) → ℝ) : 0 ≤ correctionBuffer w := by sorry
theorem correctionBuffer_le_budget {d : ℕ} (w : (Fin d → Bool) → ℝ) : correctionBuffer w ≤ coefficientBudget w := by sorry
theorem correctedLaw_nonneg {d : ℕ} (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) : ∀ x, 0 ≤ correctedLaw w x := by sorry
theorem correctedLaw_mass {d : ℕ} (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) : (∑ x, correctedLaw w x) = 1 := by sorry
theorem correctedLaw_mean {d : ℕ} (w : (Fin d → Bool) → ℝ) (i : Fin d) : (∑ x, correctedLaw w x * (bitSign (x i) : ℝ)) = 0 := by sorry
theorem correctedLaw_pair {d : ℕ} (w : (Fin d → Bool) → ℝ) (i j : Fin d) (hij : i ≠ j) : (∑ x, correctedLaw w x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) = 0 := by sorry
theorem correctedLaw_collision_identity {d : ℕ} (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) : collision (correctedLaw w) = 1 / ((2 : ℝ) ^ d) + (collision w - (1 + ∑ i : LowIndex d, fourierCoefficient w lowCharacter i ^ 2) / ((2 : ℝ) ^ d)) / (1 + correctionBuffer w) ^ 2 := by sorry
theorem correctedLaw_collision_lower {d : ℕ} (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) : collision w / (1 + correctionBuffer w) ^ 2 ≤ collision (correctedLaw w) := by sorry
theorem correctedLaw_variation_bound {d : ℕ} (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1) : (1 / 2 : ℝ) * (∑ x, |correctedLaw w x - w x|) ≤ correctionBuffer w / (1 + correctionBuffer w) := by sorry
theorem correctedLaw_input_window {d : ℕ} (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1) (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1) (hcollision : 1 / ((d : ℝ) + 4) ≤ collision w) (hbuffer : correctionBuffer w ≤ 1 / (2048 * ((d : ℝ) + 4) ^ 3)) : (0 ≤ 1 / ((d : ℝ) + 4) - collision (correctedLaw w)) ∧ (1 / ((d : ℝ) + 4) - collision (correctedLaw w) ≤ 1 / (1024 * ((d : ℝ) + 4) ^ 4)) ∧ ∃ H : Matrix (Fin (d + 4)) (Fin (d + 4)) ℝ, Matrix.IsHadamard H := by sorry
theorem correctedLaw_budget_input_window {d : ℕ} (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1) (w : (Fin d → Bool) → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : ∑ x, w x = 1) (hcollision : 1 / ((d : ℝ) + 4) ≤ collision w) (hbudget : coefficientBudget w ≤ 1 / (2048 * ((d : ℝ) + 4) ^ 3)) : ∃ H : Matrix (Fin (d + 4)) (Fin (d + 4)) ℝ, Matrix.IsHadamard H := by sorry
theorem uniform_candidate_correction_obstruction {d : ℕ} (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1) (G : Finset (Fin d → Bool)) (hcard : G.card = d + 4) (hnonzero : ∃ i : LowIndex d, fourierCoefficient (uniformOn G (d + 4)) lowCharacter i ≠ 0) : 1 / (2 * ((d : ℝ) + 4) ^ 2) ≤ 1 / ((d : ℝ) + 4) - collision (correctedLaw (uniformOn G (d + 4))) := by sorry
theorem uniform_candidate_misses_extraction_window {d : ℕ} (hd : 4 ≤ d) (hres : (d + 1) % 4 = 1) (G : Finset (Fin d → Bool)) (hcard : G.card = d + 4) (hnonzero : ∃ i : LowIndex d, fourierCoefficient (uniformOn G (d + 4)) lowCharacter i ≠ 0) : 1 / (1024 * ((d : ℝ) + 4) ^ 4) < 1 / ((d : ℝ) + 4) - collision (correctedLaw (uniformOn G (d + 4))) := by sorry
theorem minimal_support_uniform_rigidity {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 3 ≤ n) (hcard : Fintype.card α ≤ roundedDimension n) (A : α → Fin n → ℤ) (w : α → ℝ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hw : ∀ a, 0 ≤ w a) (hmass : ∑ a, w a = 1) (hiso : ∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) : Fintype.card α = roundedDimension n ∧ (∀ a, w a = 1 / (roundedDimension n : ℝ)) ∧ ∃ H : Matrix (Fin (roundedDimension n)) (Fin (roundedDimension n)) ℝ, Matrix.IsHadamard H := by sorry
theorem no_reweighting_of_failed_uniform_frame {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 3 ≤ n) (hcard : Fintype.card α = roundedDimension n) (A : α → Fin n → ℤ) (hsign : ∀ a i, A a i = 1 ∨ A a i = -1) (hfailed : ¬∀ i j, (∑ a, (1 / (roundedDimension n : ℝ)) * (A a i : ℝ) * (A a j : ℝ)) = if i = j then 1 else 0) : ¬∃ w : α → ℝ, (∀ a, 0 ≤ w a) ∧ (∑ a, w a = 1) ∧ (∀ i j, ∑ a, w a * (A a i : ℝ) * (A a j : ℝ) = if i = j then 1 else 0) := by sorry
theorem straight_bridge_minimum {α : Type*} [Fintype α] (p q : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hmass : ∑ a, p a = 1) (hne : p ≠ q) (hbetter : collision p ≤ collision q) : 0 ≤ bridgeTime (collision p) (collision q) (lawOverlap p q) ∧ bridgeTime (collision p) (collision q) (lawOverlap p q) ≤ 1 / 2 ∧ collision (probabilityBlend p q (bridgeTime (collision p) (collision q) (lawOverlap p q))) = collision p - bridgeLoss (collision p) (collision q) (lawOverlap p q) ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → collision (probabilityBlend p q (bridgeTime (collision p) (collision q) (lawOverlap p q))) ≤ collision (probabilityBlend p q t)) ∧ bridgeLoss (collision p) (collision q) (lawOverlap p q) ≤ collision p ^ 2 / (collision p + collision q) ∧ collision p ^ 2 / (collision p + collision q) ≤ collision p / 2 := by sorry
theorem straight_bridge_monotone {α : Type*} [Fintype α] (p q : α → ℝ) (hne : p ≠ q) (hca : collision p ≤ lawOverlap p q) : MonotoneOn (fun t : ℝ => collision (probabilityBlend p q t)) (Set.Ici 0) := by sorry
theorem disjoint_bridge_loss_sharp {α : Type*} [Fintype α] (p q : α → ℝ) (_hp : ∀ a, 0 ≤ p a) (hdisjoint : ∀ a, p a = 0 ∨ q a = 0) : bridgeLoss (collision p) (collision q) (lawOverlap p q) = collision p ^ 2 / (collision p + collision q) := by sorry
theorem probabilityBlend_feasible {α ι : Type*} [Fintype α] (p q : α → ℝ) (φ : ι → α → ℝ) (k : ι → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) (hmassp : ∑ a, p a = 1) (hmassq : ∑ a, q a = 1) (hmomentp : ∀ i, ∑ a, p a * φ i a = k i) (hmomentq : ∀ i, ∑ a, q a * φ i a = k i) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) : (∀ a, 0 ≤ probabilityBlend p q t a) ∧ (∑ a, probabilityBlend p q t a = 1) ∧ (∀ i, ∑ a, probabilityBlend p q t a * φ i a = k i) := by sorry
theorem full_rank_positive_correction {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α] [DecidableEq ι] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (hA : A.rank = Fintype.card ι) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) (hb : b i₀ = 1) (τ : ℝ) (hτ : 0 ≤ τ) (hres : ∀ i, |A.mulVec p i - b i| ≤ τ) (hmargin : ∀ a, supportCondition A * τ ≤ p a) : (∀ a, 0 ≤ supportCorrection A b p a) ∧ (∑ a, supportCorrection A b p a = 1) ∧ A.mulVec (supportCorrection A b p) = b ∧ (∀ a, |supportCorrection A b p a - p a| ≤ supportCondition A * τ) ∧ (∑ a, |supportCorrection A b p a - p a|) / 2 ≤ Fintype.card α * supportCondition A * τ / 2 ∧ collision p - 2 * supportCondition A * τ ≤ collision (supportCorrection A b p) := by sorry
theorem supportCorrection_input_window {ι α : Type*} [Fintype ι] [Fintype α] [Nonempty α] [DecidableEq ι] [DecidableEq α] {n : ℕ} (hn : 5 ≤ n) (hresidue : n % 4 = 1) (V : α → Fin n → ℤ) (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hsign : ∀ a i, V a i = 1 ∨ V a i = -1) (hcoordinates : ∀ i j, ∃ r, (∀ a, A r a = (V a i : ℝ) * (V a j : ℝ)) ∧ b r = if i = j then 1 else 0) (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (hA : A.rank = Fintype.card ι) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) (hb : b i₀ = 1) (τ : ℝ) (hτ : 0 ≤ τ) (hres : ∀ i, |A.mulVec p i - b i| ≤ τ) (hmargin : ∀ a, supportCondition A * τ ≤ p a) (hcollision : 1 / ((n : ℝ) + 3) ≤ collision p) (hsmall : supportCondition A * τ ≤ 1 / (2048 * ((n : ℝ) + 3) ^ 4)) : ∃ H : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ, Matrix.IsHadamard H := by sorry
theorem walsh_inversion {d : ℕ} (w : (Fin d → Bool) → ℝ) (x : Fin d → Bool) : (∑ S : Finset (Fin d), walshCoefficient w S * (walshChar S x : ℝ)) = (2 : ℝ) ^ d * w x := by sorry
theorem walsh_parseval {d : ℕ} (w : (Fin d → Bool) → ℝ) : (∑ S : Finset (Fin d), walshCoefficient w S ^ 2) = (2 : ℝ) ^ d * collision w := by sorry
theorem observed_moments_iff_mask_cover {d : ℕ} (B : Finset (Finset (Fin d))) (hB : ∅ ∉ B) (w : (Fin d → Bool) → ℝ) : ((∀ S ∈ B, walshCoefficient w S = 0) ∧ (∀ S ∈ B, ∀ T ∈ B, S ≠ T → ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0)) ↔ ∀ c ∈ maskSumset (insert ∅ B), c ≠ ∅ → walshCoefficient w c = 0 := by sorry
theorem full_mask_cover_uniform {d : ℕ} (B : Finset (Finset (Fin d))) (hB : ∅ ∉ B) (hcover : maskSumset (insert ∅ B) = Finset.univ) (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) (hmoments : (∀ S ∈ B, walshCoefficient w S = 0) ∧ (∀ S ∈ B, ∀ T ∈ B, S ≠ T → ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0)) : ∀ x, w x = 1 / (2 : ℝ) ^ d := by sorry
theorem more_than_half_mask_cover {d : ℕ} (A : Finset (Finset (Fin d))) (hlarge : 2 ^ d < 2 * A.card) : maskSumset A = Finset.univ := by sorry
theorem characterTilt_endpoint_uniform {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) (e : ℤ) (he : e = 1 ∨ e = -1) : (characterLevel c e).card = 2 ^ d / 2 ∧ ∀ x, characterTilt c (e : ℝ) x = if x ∈ characterLevel c e then 1 / ((characterLevel c e).card : ℝ) else 0 := by sorry
theorem binarySeed_bijective {d : ℕ} : Function.Bijective (@binarySeed d) := by sorry
theorem characterLevel_linear_fiber {d : ℕ} (c : Finset (Fin d)) (x : Fin d → Bool) : (x ∈ characterLevel c 1 ↔ maskFunctional c (binarySeed x) = 0) ∧ (x ∈ characterLevel c (-1) ↔ maskFunctional c (binarySeed x) = 1) := by sorry
theorem maskFunctional_nonzero {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) : maskFunctional c ≠ 0 := by sorry
theorem maskFunctional_kernel_dimension {d : ℕ} (c : Finset (Fin d)) (hc : c.Nonempty) : Module.finrank (ZMod 2) (LinearMap.ker (maskFunctional c)) = d - 1 := by sorry
theorem missing_direction_laws {d : ℕ} (B : Finset (Finset (Fin d))) (hB : ∅ ∉ B) (c : Finset (Fin d)) (hmissing : c ∉ maskSumset (insert ∅ B)) (t : ℝ) (ht : -1 ≤ t) (ht' : t ≤ 1) : (∀ x, 0 ≤ characterTilt c t x) ∧ (∑ x, characterTilt c t x = 1) ∧ (∀ S ∈ B, walshCoefficient (characterTilt c t) S = 0) ∧ (∀ S ∈ B, ∀ T ∈ B, S ≠ T → ∑ x, characterTilt c t x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) ∧ collision (characterTilt c t) = (1 + t ^ 2) / (2 : ℝ) ^ d := by sorry
theorem spanning_characters_injective {d : ℕ} (B : Finset (Finset (Fin d))) (hspan : Submodule.span (ZMod 2) (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤) : Function.Injective (fun x : Fin d → Bool => fun S : B => walshChar S.val x) := by sorry
theorem characterCode_collision {d : ℕ} (B : Finset (Finset (Fin d))) (hspan : Submodule.span (ZMod 2) (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤) (w : (Fin d → Bool) → ℝ) : collision (pushLaw (characterCode B) w) = collision w := by sorry
theorem minimum_binary_seed_observed_law {r : ℕ} (B : Finset (Finset (Fin r))) (hB : ∅ ∉ B) (hminimum : r = Nat.clog 2 (B.card + 1)) (hspan : Submodule.span (ZMod 2) (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤) (w : (Fin r → Bool) → ℝ) (hmass : ∑ x, w x = 1) (hmean : ∀ S ∈ B, walshCoefficient w S = 0) (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T → ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) : (∀ x, w x = 1 / (2 : ℝ) ^ r) ∧ (∀ y, 0 ≤ pushLaw (characterCode B) w y) ∧ (∑ y, pushLaw (characterCode B) w y = 1) ∧ (∀ y, pushLaw (characterCode B) w y = 0 ∨ pushLaw (characterCode B) w y = 1 / (2 : ℝ) ^ r) ∧ (Finset.univ.filter (fun y => pushLaw (characterCode B) w y ≠ 0)).card = 2 ^ r ∧ collision (pushLaw (characterCode B) w) = 1 / (2 : ℝ) ^ r := by sorry
theorem minimal_binary_seed_gap {r : ℕ} (N : ℕ) (hN : 12 ≤ N) (hdiv : 4 ∣ N) (hnotpower : ∀ a : ℕ, N ≠ 2 ^ a) (B : Finset (Finset (Fin r))) (hB : ∅ ∉ B) (hcard : B.card = N - 4) (hminimum : r = Nat.clog 2 (B.card + 1)) (hspan : Submodule.span (ZMod 2) (Set.range (fun S : B => binarySeed (maskSeed S.val))) = ⊤) (w : (Fin r → Bool) → ℝ) (hmass : ∑ x, w x = 1) (hmean : ∀ S ∈ B, walshCoefficient w S = 0) (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T → ∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ) = 0) : 2 / (N : ℝ) ^ 2 < 1 / (N : ℝ) - collision (pushLaw (characterCode B) w) ∧ 1 / (1024 * (N : ℝ) ^ 4) < 1 / (N : ℝ) - collision (pushLaw (characterCode B) w) := by sorry
theorem approximate_mask_cover {d : ℕ} (B : Finset (Finset (Fin d))) (hcover : maskSumset (insert ∅ B) = Finset.univ) (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) (ε : ℝ) (hmean : ∀ S ∈ B, |walshCoefficient w S| ≤ ε) (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T → |∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ)| ≤ ε) : collision w = (1 + ∑ S ∈ (Finset.univ : Finset (Finset (Fin d))).erase ∅, walshCoefficient w S ^ 2) / (2 : ℝ) ^ d ∧ collision w ≤ 1 / (2 : ℝ) ^ d + ((2 : ℝ) ^ d - 1) / (2 : ℝ) ^ d * ε ^ 2 := by sorry
theorem approximate_cover_error_obstruction {d : ℕ} (B : Finset (Finset (Fin d))) (hcover : maskSumset (insert ∅ B) = Finset.univ) (w : (Fin d → Bool) → ℝ) (hmass : ∑ x, w x = 1) (ε η : ℝ) (hmean : ∀ S ∈ B, |walshCoefficient w S| ≤ ε) (hpair : ∀ S ∈ B, ∀ T ∈ B, S ≠ T → |∑ x, w x * (walshChar S x : ℝ) * (walshChar T x : ℝ)| ≤ ε) (N : ℕ) (hN : 0 < N) (hNL : (N : ℝ) < (2 : ℝ) ^ d) (hcollision : 1 / (N : ℝ) - η ≤ collision w) : ((2 : ℝ) ^ d / (N : ℝ) - 1 - (2 : ℝ) ^ d * η) / ((2 : ℝ) ^ d - 1) ≤ ε ^ 2 := by sorry
theorem trapInner_formula {s : ℕ} (e : Finset (Fin s)) (u v : (Fin s → Bool) × (Fin s → Bool)) : trapInner e u v = (if u.1 = v.1 then (2 : ℤ) ^ s else 0) + (if u.2 = v.2 then (2 : ℤ) ^ s else 0) - 1 + trapMixed e u * trapMixed e v := by sorry
theorem trapInner_zero_iff {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (u v : (Fin s → Bool) × (Fin s → Bool)) : trapInner e u v = 0 ↔ u.1 ≠ v.1 ∧ u.2 ≠ v.2 ∧ trapMixed e u = trapMixed e v := by sorry
theorem trapRow_injective {s : ℕ} (e : Finset (Fin s)) : Function.Injective (trapRow e) := by sorry
theorem trap_clique_card_le {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S) : S.card ≤ 2 ^ s := by sorry
theorem trap_maximum_clique_exists {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) : ∃ S : Finset ((Fin s → Bool) × (Fin s → Bool)), trapOrthogonal e S ∧ S.card = 2 ^ s := by sorry
theorem maximum_trap_clique_graph {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (S : Finset ((Fin s → Bool) × (Fin s → Bool))) (hS : trapOrthogonal e S) (hcard : S.card = 2 ^ s) : ∃ (π : (Fin s → Bool) ≃ (Fin s → Bool)) (c : ℤ), (c = 1 ∨ c = -1) ∧ (∀ u ∈ S, u.2 = π u.1) ∧ (∀ a, (a, π a) ∈ S) ∧ (∀ u ∈ S, trapMixed e u = c) := by sorry
theorem complete_maximum_trap_row_subset {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (U : Finset ((Finset (Fin s) ⊕ Finset (Fin s)) → ℤ)) (hsubset : ∀ r ∈ U, ∃ u : (Fin s → Bool) × (Fin s → Bool), trapRow e u = r) (horth : ∀ r ∈ U, ∀ t ∈ U, r ≠ t → ∑ j, r j * t j = 0) (hcard : U.card = 2 ^ s) : ∃ (H : Matrix (Finset (Fin s) ⊕ Finset (Fin s)) (Finset (Fin s) ⊕ Finset (Fin s)) ℝ) (rows : U ↪ (Finset (Fin s) ⊕ Finset (Fin s))), Matrix.IsHadamard H ∧ (∀ r j, H (rows r) j = (r.val j : ℝ)) ∧ (trapRowIndices e H).card = 2 ^ s := by sorry
theorem trap_columns_orthogonal {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (i j : Finset (Fin s) ⊕ Finset (Fin s)) : (∑ u : (Fin s → Bool) × (Fin s → Bool), trapRow e u i * trapRow e u j) = if i = j then (2 : ℤ) ^ (2 * s) else 0 := by sorry
theorem trapCode_injective {s : ℕ} (e : Finset (Fin s)) : Function.Injective (trapCode e) := by sorry
theorem trapLaw_probability {s : ℕ} (e : Finset (Fin s)) : (∀ x, 0 ≤ trapLaw e x) ∧ (∑ x, trapLaw e x) = 1 := by sorry
theorem trapLaw_weights {s : ℕ} (e : Finset (Fin s)) : ∀ x, trapLaw e x = 0 ∨ trapLaw e x = 1 / (2 : ℝ) ^ (2 * s) := by sorry
theorem trapLaw_support_card {s : ℕ} (e : Finset (Fin s)) : (Finset.univ.filter (fun x => trapLaw e x ≠ 0)).card = 2 ^ (2 * s) := by sorry
theorem trapLaw_collision {s : ℕ} (e : Finset (Fin s)) : collision (trapLaw e) = 1 / (2 : ℝ) ^ (2 * s) := by sorry
theorem trapLaw_mean {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (j : TrapCoordinate s) : (∑ x : TrapCoordinate s → Bool, trapLaw e x * (bitSign (x j) : ℝ)) = 0 := by sorry
theorem trapLaw_pair {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (i j : TrapCoordinate s) (hij : i ≠ j) : (∑ x : TrapCoordinate s → Bool, trapLaw e x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) = 0 := by sorry
theorem endpointCode_injective {s : ℕ} : Function.Injective (@endpointCode s) := by sorry
theorem endpointLaw_probability (s : ℕ) : (∀ x, 0 ≤ endpointLaw s x) ∧ (∑ x, endpointLaw s x) = 1 := by sorry
theorem endpointLaw_weights (s : ℕ) : ∀ x, endpointLaw s x = 0 ∨ endpointLaw s x = 1 / (2 * (2 : ℝ) ^ s) := by sorry
theorem endpointLaw_support_card (s : ℕ) : (Finset.univ.filter (fun x => endpointLaw s x ≠ 0)).card = 2 * 2 ^ s := by sorry
theorem endpointLaw_collision (s : ℕ) : collision (endpointLaw s) = 1 / (2 * (2 : ℝ) ^ s) := by sorry
theorem endpointLaw_mean {s : ℕ} (j : TrapCoordinate s) : (∑ x : TrapCoordinate s → Bool, endpointLaw s x * (bitSign (x j) : ℝ)) = 0 := by sorry
theorem endpointLaw_pair {s : ℕ} (i j : TrapCoordinate s) (hij : i ≠ j) : (∑ x : TrapCoordinate s → Bool, endpointLaw s x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ)) = 0 := by sorry
theorem trap_endpoint_code_eq_iff {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (a b c : Fin s → Bool) (t : Bool) : trapCode e (a, b) = endpointCode (c, t) ↔ a = c ∧ b = c ∧ t = false := by sorry
theorem trap_endpoint_lawOverlap {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) : lawOverlap (trapLaw e) (endpointLaw s) = 1 / (2 * (2 : ℝ) ^ (2 * s)) := by sorry
theorem trap_endpoint_common_atoms {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) : (Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ endpointLaw s x ≠ 0)).card = 2 ^ s := by sorry
theorem trap_bridge_collision {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (t : ℝ) : collision (probabilityBlend (trapLaw e) (endpointLaw s) t) = (1 - t + ((2 : ℝ) ^ s / 2) * t ^ 2) / (2 : ℝ) ^ (2 * s) := by sorry
theorem trap_bridge_minimum {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) : (0 ≤ 1 / (2 : ℝ) ^ s ∧ 1 / (2 : ℝ) ^ s ≤ 1) ∧ collision (probabilityBlend (trapLaw e) (endpointLaw s) (1 / (2 : ℝ) ^ s)) = (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) ∧ (∀ t : ℝ, (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) ≤ collision (probabilityBlend (trapLaw e) (endpointLaw s) t)) := by sorry
theorem trap_bridge_exact_loss {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) : collision (trapLaw e) - collision (probabilityBlend (trapLaw e) (endpointLaw s) (1 / (2 : ℝ) ^ s)) = 1 / (2 * ((2 : ℝ) ^ s) ^ 3) := by sorry
theorem trap_bridge_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) : (∀ x, 0 ≤ probabilityBlend (trapLaw e) (endpointLaw s) t x) ∧ (∑ x, probabilityBlend (trapLaw e) (endpointLaw s) t x) = 1 ∧ (∀ j : TrapCoordinate s, ∑ x, probabilityBlend (trapLaw e) (endpointLaw s) t x * (bitSign (x j) : ℝ) = 0) ∧ (∀ i j : TrapCoordinate s, i ≠ j → ∑ x, probabilityBlend (trapLaw e) (endpointLaw s) t x * (bitSign (x i) : ℝ) * (bitSign (x j) : ℝ) = 0) := by sorry
theorem trap_coordinate_card (s : ℕ) : Fintype.card (TrapCoordinate s) = 2 * 2 ^ s - 1 := by sorry
theorem endpointLaw_global_maximum (s : ℕ) : observedFeasible (endpointLaw s) ∧ ∀ w : (TrapCoordinate s → Bool) → ℝ, observedFeasible w → collision w ≤ collision (endpointLaw s) := by sorry
theorem observed_optimizer_uniform {s : ℕ} (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w) (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) : ∀ x, w x = 0 ∨ w x = 1 / (2 * (2 : ℝ) ^ s) := by sorry
theorem optimizer_common_trap_atoms_bound {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w) (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) : (Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ w x ≠ 0)).card ≤ 2 ^ s := by sorry
theorem optimizer_bridge_comparison {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w) (heq : collision w = 1 / (2 * (2 : ℝ) ^ s)) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) : collision (probabilityBlend (trapLaw e) w t) ≤ collision (probabilityBlend (trapLaw e) (endpointLaw s) t) := by sorry
theorem trap_bridge_optimal_among_global_maximizers {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (w : (TrapCoordinate s → Bool) → ℝ) (hw : observedFeasible w) (hmax : ∀ q : (TrapCoordinate s → Bool) → ℝ, observedFeasible q → collision q ≤ collision w) : (Finset.univ.filter (fun x => trapLaw e x ≠ 0 ∧ w x ≠ 0)).card ≤ 2 ^ s ∧ collision (probabilityBlend (trapLaw e) w (1 / (2 : ℝ) ^ s)) ≤ (1 - 1 / (2 * (2 : ℝ) ^ s)) / (2 : ℝ) ^ (2 * s) := by sorry
theorem linearLaw_probability {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W] (L : V →ₗ[ZMod 2] W) : (∀ y, 0 ≤ linearLaw L y) ∧ (∑ y, linearLaw L y) = 1 := by sorry
theorem linearLaw_collision {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W] (L : V →ₗ[ZMod 2] W) : collision (linearLaw L) = 1 / (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range L) := by sorry
theorem linearLaw_support_card {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W] (L : V →ₗ[ZMod 2] W) : (Finset.univ.filter (fun y => linearLaw L y ≠ 0)).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.range L) := by sorry
theorem linearLaw_collision_antitone_rank {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W] (L M : V →ₗ[ZMod 2] W) (hrank : Module.finrank (ZMod 2) (LinearMap.range M) ≤ Module.finrank (ZMod 2) (LinearMap.range L)) : collision (linearLaw L) ≤ collision (linearLaw M) := by sorry
theorem linearLaw_single_rank_step {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Module (ZMod 2) V] [Module (ZMod 2) W] [Fintype V] [Fintype W] (L M : V →ₗ[ZMod 2] W) (hrank : Module.finrank (ZMod 2) (LinearMap.range L) = Module.finrank (ZMod 2) (LinearMap.range M) ∨ Module.finrank (ZMod 2) (LinearMap.range L) = Module.finrank (ZMod 2) (LinearMap.range M) + 1) : (collision (linearLaw M) = collision (linearLaw L) ∧ (Finset.univ.filter (fun y => linearLaw M y ≠ 0)).card = (Finset.univ.filter (fun y => linearLaw L y ≠ 0)).card) ∨ (collision (linearLaw M) = 2 * collision (linearLaw L) ∧ 2 * (Finset.univ.filter (fun y => linearLaw M y ≠ 0)).card = (Finset.univ.filter (fun y => linearLaw L y ≠ 0)).card) := by sorry
theorem rewireMask_injective {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (T : Finset (Finset (Fin s))) : Function.Injective (rewireMask e T) := by sorry
theorem rewireMask_observed_nonzero {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (T : Finset (Finset (Fin s))) (j : TrapCoordinate s) : rewireMask e T j.val ≠ (∅, ∅) := by sorry
theorem rewireMask_initial_swap {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) : rewireMask e ∅ = trapMask e ∘ initialSwapIndex e := by sorry
theorem maskPairLaw_feasible {s : ℕ} (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) (hinj : Function.Injective M) (hzero : M (Sum.inl ∅) = (∅, ∅)) : observedFeasible (maskPairLaw M) := by sorry
theorem rewireLaw_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (T : Finset (Finset (Fin s))) : observedFeasible (rewireLaw e T) := by sorry
theorem rewireCode_unchanged_column {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) (u : (Fin s → Bool) × (Fin s → Bool)) (j : TrapCoordinate s) (hj : j.val ≠ Sum.inr b) : maskPairCode (rewireMask e (insert b T)) u j = maskPairCode (rewireMask e T) u j := by sorry
theorem rewireCode_new_column {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) (u : (Fin s → Bool) × (Fin s → Bool)) (j : TrapCoordinate s) (hj : j.val = Sum.inr b) : bitSign (maskPairCode (rewireMask e (insert b T)) u j) = walshChar b u.1 * walshChar e u.2 := by sorry
theorem rewireLaw_final {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) : rewireLaw e Finset.univ = endpointLaw s := by sorry
theorem rewiringList_nodup {s : ℕ} (e : Finset (Fin s)) : (rewiringList e).Nodup := by sorry
theorem rewiringList_members {s : ℕ} (e b : Finset (Fin s)) : b ∈ rewiringList e ↔ b ≠ ∅ ∧ b ≠ e := by sorry
theorem rewiring_total_jumps {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : (rewiringList e).length + 1 = 2 ^ s - 1 := by sorry
theorem rewiringSchedule_mask_step {s : ℕ} (e : Finset (Fin s)) (k : ℕ) (hk : k < (rewiringList e).length) : rewireMask e (rewiringPrefix e (k + 1)) = Function.update (rewireMask e (rewiringPrefix e k)) (Sum.inr (rewiringList e)[k]) ((rewiringList e)[k], e) := by sorry
theorem rewiringSchedule_feasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) (k : ℕ) : observedFeasible (rewiringScheduleLaw e k) := by sorry
theorem rewiringSchedule_initial {s : ℕ} (e : Finset (Fin s)) : rewiringScheduleLaw e 0 = rewireLaw e ∅ := by sorry
theorem rewiringSchedule_final {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) : rewiringScheduleLaw e (rewiringList e).length = endpointLaw s := by sorry
theorem maskPairLaw_rank_collision {s : ℕ} (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) : collision (maskPairLaw M) = 1 / (2 : ℝ) ^ Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear M)) := by sorry
theorem maskPairLaw_rank_support {s : ℕ} (M : (Finset (Fin s) ⊕ Finset (Fin s)) → Finset (Fin s) × Finset (Fin s)) : (Finset.univ.filter (fun x => maskPairLaw M x ≠ 0)).card = 2 ^ Module.finrank (ZMod 2) (LinearMap.range (maskPairLinear M)) := by sorry
theorem rewire_encoder_step {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) : maskPairLinear (rewireMask e (insert b T)) = (rewireRepair b hb).comp (maskPairLinear (rewireMask e T)) := by sorry
theorem rewireLaw_step_dichotomy {s : ℕ} (e b : Finset (Fin s)) (T : Finset (Finset (Fin s))) (hb : b ≠ ∅) : (collision (rewireLaw e (insert b T)) = collision (rewireLaw e T) ∧ (Finset.univ.filter (fun x => rewireLaw e (insert b T) x ≠ 0)).card = (Finset.univ.filter (fun x => rewireLaw e T x ≠ 0)).card) ∨ (collision (rewireLaw e (insert b T)) = 2 * collision (rewireLaw e T) ∧ 2 * (Finset.univ.filter (fun x => rewireLaw e (insert b T) x ≠ 0)).card = (Finset.univ.filter (fun x => rewireLaw e T x ≠ 0)).card) := by sorry
theorem rewiringSchedule_collision_nondecreasing {s : ℕ} (e : Finset (Fin s)) (k : ℕ) (hk : k < (rewiringList e).length) : collision (rewiringScheduleLaw e k) ≤ collision (rewiringScheduleLaw e (k + 1)) := by sorry
theorem rewiringRank_initial {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) : rewiringRank e 0 = 2 * s := by sorry
theorem rewiringRank_final {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) : rewiringRank e (rewiringList e).length = s + 1 := by sorry
theorem rewiring_support_halving_jump_count {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : ((Finset.range (rewiringList e).length).filter (fun k => 2 * (Finset.univ.filter (fun x => rewiringScheduleLaw e (k + 1) x ≠ 0)).card = (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card ∧ collision (rewiringScheduleLaw e (k + 1)) = 2 * collision (rewiringScheduleLaw e k))).card = s - 1 := by sorry
theorem rewiring_support_preserving_jump_count {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : ((Finset.range (rewiringList e).length).filter (fun k => (Finset.univ.filter (fun x => rewiringScheduleLaw e (k + 1) x ≠ 0)).card = (Finset.univ.filter (fun x => rewiringScheduleLaw e k x ≠ 0)).card ∧ collision (rewiringScheduleLaw e (k + 1)) = collision (rewiringScheduleLaw e k))).card + 1 = 2 ^ s - s := by sorry
theorem initial_swap_preserves_support_collision {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) : collision (rewiringScheduleLaw e 0) = collision (trapLaw e) ∧ (Finset.univ.filter (fun x => rewiringScheduleLaw e 0 x ≠ 0)).card = (Finset.univ.filter (fun x => trapLaw e x ≠ 0)).card := by sorry
theorem rewiringSchedule_segment_bound {s : ℕ} (e : Finset (Fin s)) (k : ℕ) (hk : k < (rewiringList e).length) (t : ℝ) : (3 / 4 : ℝ) * collision (rewiringScheduleLaw e k) ≤ collision (probabilityBlend (rewiringScheduleLaw e k) (rewiringScheduleLaw e (k + 1)) t) := by sorry
theorem initial_swap_lawOverlap {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : lawOverlap (trapLaw e) (rewireLaw e ∅) = 1 / (2 * (2 : ℝ) ^ (2 * s)) := by sorry
theorem initial_swap_bridge_collision {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) (t : ℝ) : collision (probabilityBlend (trapLaw e) (rewireLaw e ∅) t) = (1 - t + t ^ 2) / (2 : ℝ) ^ (2 * s) := by sorry
theorem initial_swap_bridge_minimum {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : collision (probabilityBlend (trapLaw e) (rewireLaw e ∅) (1 / 2)) = 3 / (4 * (2 : ℝ) ^ (2 * s)) ∧ ∀ t : ℝ, 3 / (4 * (2 : ℝ) ^ (2 * s)) ≤ collision (probabilityBlend (trapLaw e) (rewireLaw e ∅) t) := by sorry
theorem rewiringPath_start {s : ℕ} (e : Finset (Fin s)) : rewiringPath e 0 0 = trapLaw e := by sorry
theorem rewiringPath_join {s : ℕ} (e : Finset (Fin s)) (k : Fin (rewiringList e).length) : rewiringPath e k.castSucc 1 = rewiringPath e k.succ 0 := by sorry
theorem rewiringPath_finish {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : rewiringPath e (Fin.last (rewiringList e).length) 1 = endpointLaw s := by sorry
theorem rewiringPath_minimum {s : ℕ} (hs : 2 ≤ s) (e : Finset (Fin s)) (he : e.Nonempty) : (∀ j : Fin ((rewiringList e).length + 1), ∀ t : ℝ, 0 ≤ t → t ≤ 1 → observedFeasible (rewiringPath e j t) ∧ 3 / (4 * (2 : ℝ) ^ (2 * s)) ≤ collision (rewiringPath e j t)) ∧ collision (rewiringPath e 0 (1 / 2)) = 3 / (4 * (2 : ℝ) ^ (2 * s)) := by sorry
theorem rewiringPath_affine {s : ℕ} (e : Finset (Fin s)) (j : Fin ((rewiringList e).length + 1)) (t : ℝ) (x : TrapCoordinate s → Bool) : rewiringPath e j t x = (1 - t) * rewiringPath e j 0 x + t * rewiringPath e j 1 x := by sorry
namespace FieldReduction
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
def collision {α : Type*} [Fintype α] (p : α → K) : K := ∑ a, p a ^ 2
def lawOverlap {α : Type*} [Fintype α] (p z : α → K) : K := ∑ a, p a * z a
noncomputable def activeSupport {α : Type*} [Fintype α] (p : α → K) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => p a ≠ 0)
def feasibleLaw {ι α : Type*} [Fintype α] (A : Matrix ι α K)
    (b : ι → K) (p : α → K) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧ A.mulVec p = b
def reductionStep {ι α : Type*} [Fintype α] (A : Matrix ι α K)
    (b : ι → K) (p q : α → K) : Prop :=
  feasibleLaw A b q ∧ collision p < collision q ∧
    activeSupport q ⊆ activeSupport p ∧ (activeSupport q).card < (activeSupport p).card ∧
    0 ≤ lawOverlap p (q - p)
theorem reductionStep_exact_endpoint {ι α : Type*} [Fintype ι] [Fintype α] (A : Matrix ι α K) (b : ι → K) (p q : α → K) (hp : feasibleLaw A b p) (hstep : reductionStep A b p q) : ∃ z : α → K, z ≠ 0 ∧ A.mulVec z = 0 ∧ 0 ≤ lawOverlap p z ∧ q = (fun a => p a + z a) ∧ (∀ a, z a < 0 → 1 ≤ p a / (-z a)) ∧ (∃ a, z a < 0 ∧ p a / (-z a) = 1) := by sorry
theorem reductionStep_interpolation {ι α : Type*} [Fintype ι] [Fintype α] (A : Matrix ι α K) (b : ι → K) (p q : α → K) (hp : feasibleLaw A b p) (hstep : reductionStep A b p q) : (∀ u : K, 0 ≤ u → u ≤ 1 → feasibleLaw A b (fun a => p a + u * (q - p) a)) ∧ MonotoneOn (fun u : K => collision (fun a => p a + u * (q - p) a)) (Set.Ici 0) := by sorry
theorem bounded_vertex_reduction {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] (A : Matrix ι α K) (b : ι → K) (p : α → K) (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) : ∃ k : ℕ, k ≤ (activeSupport p).card - (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧ ∃ path : Fin (k + 1) → (α → K), path ⟨0, Nat.zero_lt_succ k⟩ = p ∧ (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧ path (Fin.last k) ∈ Set.extremePoints K {q | feasibleLaw A b q} ∧ (activeSupport (path (Fin.last k))).card ≤ Fintype.card ι := by sorry
theorem rational_bounded_vertex_reduction {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] (A : Matrix ι α ℚ) (b : ι → ℚ) (p : α → ℚ) (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) : ∃ k : ℕ, k ≤ (activeSupport p).card - (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧ ∃ path : Fin (k + 1) → (α → ℚ), path ⟨0, Nat.zero_lt_succ k⟩ = p ∧ (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧ path (Fin.last k) ∈ Set.extremePoints ℚ {q | feasibleLaw A b q} ∧ (activeSupport (path (Fin.last k))).card ≤ Fintype.card ι := by sorry
end FieldReduction
theorem rational_reduction_real_vertex {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] (A : Matrix ι α ℚ) (b : ι → ℚ) (p : α → ℚ) (hp : FieldReduction.feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) : ∃ k : ℕ, k ≤ (activeSupport (realLaw p)).card - ((A.map (Rat.castHom ℝ)).submatrix id (fun a : activeSupport (realLaw p) => (a : α))).rank ∧ ∃ path : Fin (k + 1) → (α → ℚ), path ⟨0, Nat.zero_lt_succ k⟩ = p ∧ (∀ j : Fin k, FieldReduction.reductionStep A b (path j.castSucc) (path j.succ)) ∧ realLaw (path (Fin.last k)) ∈ Set.extremePoints ℝ {q | feasibleLaw (A.map (Rat.castHom ℝ)) (realLaw b) q} ∧ (activeSupport (realLaw (path (Fin.last k)))).card ≤ Fintype.card ι := by sorry
end EntropyDesigns
namespace EntropyDesigns
open scoped Matrix
def positiveDiagonalScale {ι : Type*} (U : Matrix ι ι ℝ) (d e : ι → ℝ) : Matrix ι ι ℝ := fun i j => d i*U i j*e j
def bipartiteSupportEdge {ι : Type*} (U : Matrix ι ι ℝ) : (ι ⊕ ι) → (ι ⊕ ι) → Prop | Sum.inl i, Sum.inr j => U i j ≠ 0 | Sum.inr j, Sum.inl i => U i j ≠ 0 | _, _ => False
def BipartiteSupportConnected {ι : Type*} (U : Matrix ι ι ℝ) : Prop := ∀ v w,Relation.ReflTransGen (bipartiteSupportEdge U) v w
theorem positive_diagonal_balancing_rigidity {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℝ) (d e : ι → ℝ) (hd : ∀ i,0<d i) (he : ∀ i,0<e i) (hUrow : U*Uᵀ=1) (hUcol : Uᵀ*U=1) (hZrow : positiveDiagonalScale U d e*(positiveDiagonalScale U d e)ᵀ=1) (hZcol : (positiveDiagonalScale U d e)ᵀ*positiveDiagonalScale U d e=1) : positiveDiagonalScale U d e=U ∧ (BipartiteSupportConnected U → ∃ c : ℝ,0<c ∧ (∀ i,d i=c) ∧ ∀ j,e j=c⁻¹) := by sorry
end EntropyDesigns
namespace EntropyDesigns
open scoped Matrix
def allOnesMatrix (n : ℕ) (R : Type*) [One R] : Matrix (Fin n) (Fin n) R := fun _ _ => 1
def modularCounterexampleSeed (n : ℕ) (R : Type*) [Ring R] : Matrix (Fin n) (Fin n) R := allOnesMatrix n R-(2 : R) • 1
theorem modular_seed_without_sign_lift {n m : ℕ} (hn : 4<n) (hm : 3≤m) (hmod : n%m=4%m) : modularCounterexampleSeed n (ZMod m)*(modularCounterexampleSeed n (ZMod m))ᵀ=(n : ZMod m) • 1 ∧ ¬ Matrix.IsHadamard (modularCounterexampleSeed n ℝ) ∧ ¬ ∃ H : Matrix (Fin n) (Fin n) ℤ, (∀ i j,H i j=1 ∨ H i j= -1) ∧ Matrix.IsHadamard (fun i j => (H i j : ℝ)) ∧ ∀ i j,(H i j : ZMod m)=modularCounterexampleSeed n (ZMod m) i j := by sorry
theorem infinitely_many_modular_seeds_without_lifts (p : ℕ) (hp : p.Prime) (hodd : Odd p) : Set.Infinite {n : ℕ | 4 ∣ n ∧ 4<n ∧ IsUnit (modularCounterexampleSeed n (ZMod p)) ∧ ¬ ∃ H : Matrix (Fin n) (Fin n) ℤ, (∀ i j,H i j=1 ∨ H i j= -1) ∧ Matrix.IsHadamard (fun i j => (H i j : ℝ)) ∧ ∀ i j,(H i j : ZMod p)=modularCounterexampleSeed n (ZMod p) i j} := by sorry
end EntropyDesigns
namespace EntropyDesigns
theorem residue_two_cube_collision_sharp {d : ℕ} (hd : 5≤d) (hres : (d+1)%4=2) (w : (Fin d → Bool) → ℝ) (hw : ∀ b,0≤w b) (hmass : ∑ b,w b=1) (hmean : ∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0) (hpair : ∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) : collision w≤1/((d : ℝ)+3) ∧ ((∃ H : Matrix (Fin (d+3)) (Fin (d+3)) ℝ,Matrix.IsHadamard H) → ∃ v : (Fin d → Bool) → ℝ, (∀ b,0≤v b) ∧ (∑ b,v b=1) ∧ (∀ i,∑ b,v b*(bitSign (b i) : ℝ)=0) ∧ (∀ i j,i≠j → ∑ b,v b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) ∧ collision v=1/((d : ℝ)+3)) := by sorry
end EntropyDesigns
namespace EntropyDesigns
theorem parity_collision_equality_two_column_iff {d : ℕ} (hd : 5≤d) (hres : (d+1)%4=2) (w : (Fin d → Bool) → ℝ) (hw : ∀ b,0≤w b) (hmass : ∑ b,w b=1) (hmean : ∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0) (hpair : ∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) : collision w=1/((d+3 : ℕ) : ℝ) ↔ (∀ b,w b=0 ∨ w b=1/((d+3 : ℕ) : ℝ)) ∧ (Finset.univ.filter (fun b => w b ≠ 0)).card=d+3 ∧ ∃ (H : Matrix (Fin (d+3)) (Fin (d+3)) ℝ) (columns : Fin (d+1) ↪ Fin (d+3)) (rows : {b // w b ≠ 0} ≃ Fin (d+3)), Matrix.IsHadamard H ∧ ∀ b i,H (rows b) (columns i)= (augmentedSign (fun (b : Fin d → Bool) i => bitSign (b i)) (b : Fin d → Bool) i : ℝ) := by sorry
theorem parity_collision_attainment_iff_hadamard {d : ℕ} (hd : 5≤d) (hres : (d+1)%4=2) : (∃ w : (Fin d → Bool) → ℝ, (∀ b,0≤w b) ∧ (∑ b,w b=1) ∧ (∀ i,∑ b,w b*(bitSign (b i) : ℝ)=0) ∧ (∀ i j,i≠j → ∑ b,w b*(bitSign (b i) : ℝ)*(bitSign (b j) : ℝ)=0) ∧ collision w=1/((d+3 : ℕ) : ℝ)) ↔ ∃ H : Matrix (Fin (d+3)) (Fin (d+3)) ℝ,Matrix.IsHadamard H := by sorry
end EntropyDesigns
namespace EntropyDesigns
noncomputable def cubeMinEntropy {d : ℕ} (w : (Fin d → Bool) → ℝ) : ℝ := -Real.log (Finset.univ.sup' Finset.univ_nonempty w)
theorem even_dimension_saturated_atom (n : ℕ) (hn : 4≤n) (heven : Even n) : ∃ w : (Fin (n-1) → Bool) → ℝ, (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧ (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧ (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) ∧ w (fun _ => false)=1/(n : ℝ) ∧ cubeMinEntropy w=Real.log (n : ℝ) := by sorry
theorem no_real_hadamard_order_six : ¬ ∃ H : Matrix (Fin 6) (Fin 6) ℝ,Matrix.IsHadamard H := by sorry
end EntropyDesigns
namespace EntropyDesigns
noncomputable def hammingWeight {d : ℕ} (x : Fin d → Bool) : ℕ := (Finset.univ.filter (fun i => x i=true)).card
def IsBinaryStrengthTwo {N d : ℕ} (rows : Fin N → Fin d → Bool) : Prop := ∀ i j,i≠j → ∀ a b : Bool, 4*(Finset.univ.filter (fun r => rows r i=a ∧ rows r j=b)).card=N
theorem pairwise_independent_weight_lower {d K : ℕ} (hd : 0<d) (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) (hweight : ∀ x,0<w x → hammingWeight x≤K) : (d+2)/2≤K := by sorry
theorem sharp_weight_integer_array_attained (d : ℕ) (hd : 2≤d) : ∃ (N : ℕ) (rows : Fin N → Fin d → Bool), 0<N ∧ IsBinaryStrengthTwo rows ∧ (∀ r,hammingWeight (rows r)≤(d+2)/2) ∧ ∃ r,hammingWeight (rows r)=(d+2)/2 := by sorry
end EntropyDesigns
namespace EntropyDesigns
def cubeOutside {d : ℕ} (T : Finset (Fin d)) (base x : Fin d → Bool) : Prop := ∀ i,i∉T → x i=base i
noncomputable def coordinateCubeMove {d : ℕ} (T : Finset (Fin d)) (base x : Fin d → Bool) : ℤ := by
  classical
  exact if cubeOutside T base x then walshChar T x else 0
def arrayMultiplicity {N d : ℕ} (rows : Fin N → Fin d → Bool) (x : Fin d → Bool) : ℕ := (Finset.univ.filter (fun r => rows r=x)).card
theorem saturated_coordinate_cube_isolation {d : ℕ} (hd : 7≤d) (rows : Fin (d+1) → Fin d → Bool) (hOA : IsBinaryStrengthTwo rows) (T : Finset (Fin d)) (hT : 3≤T.card) (base : Fin d → Bool) (z : ℤ) (hz : z≠0) : ∃ x : Fin d → Bool,(arrayMultiplicity rows x : ℤ)+z*coordinateCubeMove T base x<0 := by sorry
end EntropyDesigns
namespace EntropyDesigns
open scoped Matrix
def binaryObservationMatrix {N d : ℕ} (rows : Fin N → Fin d → Bool) : Matrix (Fin N) (Fin d) (ZMod 2) := fun r i => if rows r i then 1 else 0
theorem minimal_target_binary_rank {N : ℕ} (hN : 12≤N) (hres : N%8=4) (rows : Fin N → Fin (N-4) → Bool) (hOA : IsBinaryStrengthTwo rows) : (binaryObservationMatrix rows)ᵀ*binaryObservationMatrix rows= (1 : Matrix (Fin (N-4)) (Fin (N-4)) (ZMod 2))+allOnesMatrix (N-4) (ZMod 2) ∧ Matrix.rank (binaryObservationMatrix rows)=N-4 := by sorry
end EntropyDesigns
namespace EntropyDesigns
noncomputable def uniformFiniteLaw {α : Type*} [DecidableEq α] (S : Finset α) (x : α) : ℝ := if x∈S then 1/(S.card : ℝ) else 0
noncomputable def totalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ := (1/2 : ℝ)*(∑ x,|p x-q x|)
theorem minimal_support_code_rigidity {N r : ℕ} (hN : 12≤N) (hres : N%8=4) (C : Submodule (ZMod 2) (Fin (N-4) → ZMod 2)) (hC : Module.finrank (ZMod 2) C≤r) (S : Finset (Fin (N-4) → Bool)) (hS : S.card=N) (hSC : ∀ x∈S,binarySeed x∈C) (q : (Fin (N-4) → Bool) → ℝ) (hq : ∀ x,0≤q x) (hmass : ∑ x,q x=1) (hmean : ∀ i,∑ x,q x*(bitSign (x i) : ℝ)=0) (hpair : ∀ i j,i≠j → ∑ x,q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) (hcard : (activeSupport q).card≤N) : (S∩activeSupport q).card≤r+4 ∧ 1-((r+4 : ℕ) : ℝ)/(N : ℝ)≤totalVariation (uniformFiniteLaw S) q ∧ N-r-4≤(activeSupport q \ S).card ∧ (activeSupport q).card=N ∧ ∀ x : activeSupport q,q x=1/(N : ℝ) := by sorry
end EntropyDesigns
namespace EntropyDesigns
def initialMask (r : ℕ) {d : ℕ} (i : Fin d) : Finset (Fin r) := Finset.univ.filter (fun j => (i.val+1).testBit j.val=true)
def initialCharacterCode {r : ℕ} (d : ℕ) (x : Fin r → Bool) : Fin d → Bool := fun i => decide (walshChar (initialMask r i) x= -1)
noncomputable def walshSubsetLaw {r : ℕ} (d : ℕ) (A : Finset (Fin r → Bool)) : (Fin d → Bool) → ℝ := pushLaw (initialCharacterCode d) (uniformFiniteLaw A)
theorem walsh_subset_candidate_full {r N : ℕ} (hN : 12≤N) (hres : N%8=4) (hNL : N≤2^r) (hhalf : 2^r/2≤N-4) (A : Finset (Fin r → Bool)) (hA : A.card=N) : (∀ y,0≤walshSubsetLaw (N-4) A y) ∧ (∑ y,walshSubsetLaw (N-4) A y)=1 ∧ (activeSupport (walshSubsetLaw (N-4) A)).card=N ∧ collision (walshSubsetLaw (N-4) A)=1/(N : ℝ) ∧ (∀ i,|∑ y,walshSubsetLaw (N-4) A y*(bitSign (y i) : ℝ)|≤((2 : ℝ)^r-(N : ℝ))/(N : ℝ)) ∧ (∀ i j,i≠j → |∑ y,walshSubsetLaw (N-4) A y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ)|≤((2 : ℝ)^r-(N : ℝ))/(N : ℝ)) ∧ totalVariation (walshSubsetLaw (N-4) A) (walshSubsetLaw (r := r) (N-4) Finset.univ)=1-(N : ℝ)/(2 : ℝ)^r ∧ collision (walshSubsetLaw (r := r) (N-4) Finset.univ)=1/(2 : ℝ)^r ∧ (∀ y,0≤walshSubsetLaw (r := r) (N-4) Finset.univ y) ∧ (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y)=1 ∧ (∀ i,(∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ))=0) ∧ (∀ i j,i≠j → (∑ y,walshSubsetLaw (r := r) (N-4) Finset.univ y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ))=0) ∧ ∀ q : (Fin (N-4) → Bool) → ℝ,(∀ y,0≤q y) → (∑ y,q y=1) → (∀ i,∑ y,q y*(bitSign (y i) : ℝ)=0) → (∀ i j,i≠j → ∑ y,q y*(bitSign (y i) : ℝ)*(bitSign (y j) : ℝ)=0) → (activeSupport q).card≤N → 1-((r+4 : ℕ) : ℝ)/(N : ℝ)≤totalVariation (walshSubsetLaw (N-4) A) q := by sorry
end EntropyDesigns
namespace EntropyDesigns
theorem paley_finite_field_exists (F : Type*) [Field F] [Fintype F] (hres : Fintype.card F%4=3) : ∃ H : Matrix (Fin (Fintype.card F+1)) (Fin (Fintype.card F+1)) ℝ,Matrix.IsHadamard H := by sorry
theorem paley_three_power_exists (t : ℕ) : ∃ H : Matrix (Fin (3^(2*t+1)+1)) (Fin (3^(2*t+1)+1)) ℝ,Matrix.IsHadamard H := by sorry
theorem paley_three_power_order_residue (t : ℕ) : (3^(2*t+1)+1)%8=4 := by sorry
end EntropyDesigns
namespace EntropyDesigns
theorem irrational_log_nine_div_log_two : Irrational (Real.log 9/Real.log 2) := by sorry
end EntropyDesigns
namespace EntropyDesigns
def exactPairwiseLaw {d : ℕ} (q : (Fin d → Bool) → ℝ) : Prop := (∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧ (∀ i,∑ x,q x*(bitSign (x i) : ℝ)=0) ∧ (∀ i j,i≠j → ∑ x,q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)
theorem paley_nonvacuous_rounding_obstruction : ∃ (N : ℕ → ℕ) (P U : (k : ℕ) → (Fin (N k-4) → Bool) → ℝ) (ε : ℕ → ℝ), Tendsto N atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧ (∀ k,12≤N k ∧ N k%8=4 ∧ (∃ H : Matrix (Fin (N k)) (Fin (N k)) ℝ,Matrix.IsHadamard H) ∧ (∀ x,0≤P k x) ∧ (∑ x,P k x)=1 ∧ (activeSupport (P k)).card=N k ∧ collision (P k)=1/(N k : ℝ) ∧ (∀ i,|∑ x,P k x*(bitSign (x i) : ℝ)|≤ε k) ∧ (∀ i j,i≠j → |∑ x,P k x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)|≤ε k) ∧ exactPairwiseLaw (U k) ∧ (∃ q : (Fin (N k-4) → Bool) → ℝ,exactPairwiseLaw q ∧ (activeSupport q).card≤N k)) ∧ Tendsto (fun k => totalVariation (P k) (U k)) atTop (𝓝 0) ∧ Tendsto (fun k => (N k : ℝ)*collision (U k)) atTop (𝓝 1) ∧ ∀ Q : (k : ℕ) → (Fin (N k-4) → Bool) → ℝ, (∀ k,exactPairwiseLaw (Q k) ∧ (activeSupport (Q k)).card≤N k) → Tendsto (fun k => totalVariation (P k) (Q k)) atTop (𝓝 1) := by sorry
end EntropyDesigns
namespace EntropyDesigns
noncomputable def tripleFamily (d : ℕ) : Finset (Finset (Fin d)) := Finset.univ.filter (fun T => T.card=3)
noncomputable def canonicalSignedCount (d L : ℕ) (S : Finset (Fin d)) : ℤ := if S.card=0 then (L : ℤ)*((d.choose 2 : ℤ)-2*d+4) else if S.card=1 then (L : ℤ)*(3-(d : ℤ)) else if S.card=2 then L else 0
noncomputable def monotoneTripleCount {d : ℕ} (L : ℕ) (t : Finset (Fin d) → ℕ) (S : Finset (Fin d)) : ℤ := canonicalSignedCount d L S+ ∑ T∈tripleFamily d,(t T : ℤ)*(if S⊆T then (-1 : ℤ)^(3-S.card) else 0)
theorem monotone_triple_conversion_classification {d L : ℕ} (hd : 4≤d) (hL : 0<L) : (∃ t : Finset (Fin d) → ℕ,∀ S,0≤monotoneTripleCount L t S) ↔ (d=4 ∧ 2≤L) ∨ (d=5 ∧ 3∣L) := by sorry
end EntropyDesigns
namespace EntropyDesigns
noncomputable section
def graphBilinear {α : Type*} [Fintype α] (R : α → α → Prop) (p q : α → ℝ) : ℝ := by
  classical
  exact ∑ a,∑ b,if R a b then p a*q b else 0
def graphEdgeMass {α : Type*} [Fintype α] (R : α → α → Prop) (w : α → ℝ) : ℝ := graphBilinear R w w
def graphNeighborMass {α : Type*} [Fintype α] (R : α → α → Prop) (w : α → ℝ) (a : α) : ℝ := by
  classical
  exact ∑ b,if R a b then w b else 0
def mergeDirection {α : Type*} [DecidableEq α] (x y : α) : α → ℝ := fun a => (if a=x then 1 else 0)-(if a=y then 1 else 0)
def mergedWeights {α : Type*} [DecidableEq α] (w : α → ℝ) (x y : α) : α → ℝ := w+w y • mergeDirection x y
def positiveGraphSupport {α : Type*} [Fintype α] (w : α → ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => 0<w a)
def graphMergeStep {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop)
    (w q : α → ℝ) : Prop :=
  ∃ x y,0<w x ∧ 0<w y ∧ x≠y ∧ ¬R x y ∧
    graphNeighborMass R w y≤graphNeighborMass R w x ∧ q=mergedWeights w x y
def hasCliqueSupport {α : Type*} [Fintype α] (R : α → α → Prop) (w : α → ℝ) : Prop :=
  ∀ x∈positiveGraphSupport w,∀ y∈positiveGraphSupport w,x≠y → R x y
def signMomentMatrix {α ι : Type*} [Fintype α] (v : α → ι → ℝ) (w : α → ℝ) : Matrix ι ι ℝ :=
  fun i j => ∑ a,w a*v a i*v a j
def signMomentError {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (v : α → ι → ℝ) (w : α → ℝ) : ℝ := ∑ i,∑ j,(signMomentMatrix v w i j-(1 : Matrix ι ι ℝ) i j)^2
def HasSupportedHadamard {α : Type*} [Fintype α] {n : ℕ}
    (A : α → Fin n → ℤ) (w : α → ℝ) : Prop :=
  ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧
    Matrix.IsHadamard (fun i j => (A (rows i) j : ℝ) : Matrix (Fin n) (Fin n) ℝ)
theorem collision_moment_sign_certificate {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 2≤n) (v : α → Fin n → ℝ) (hsign : ∀ x i,v x i=1 ∨ v x i= -1) (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (a : ℝ) (ha : 0<a) (hGap : ∀ x y,0<w x → 0<w y → x≠y → inner v x y≠0 → a^2 ≤ inner v x y^2) (hCert : ((n : ℝ)^2-a^2)*collision w>(n : ℝ)+signMomentError v w-a^2/((n : ℝ)-1)) : ∃ (q : α → ℝ) (rows : Fin n ↪ α), (∀ x,0≤q x) ∧ (∑ x,q x)=1 ∧ positiveGraphSupport q⊆positiveGraphSupport w ∧ hasCliqueSupport (fun x y => inner v x y=0) q ∧ Relation.ReflTransGen (graphMergeStep (fun x y => inner v x y=0)) w q ∧ (∀ i,rows i∈positiveGraphSupport q) ∧ Matrix.IsHadamard (fun i j => v (rows i) j : Matrix (Fin n) (Fin n) ℝ) := by sorry
theorem even_sign_collision_rounding {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 4≤n) (hEven : n%2=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1) (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hCert : ((n : ℝ)^2-4)*collision w>(n : ℝ)+signMomentError (fun x i => (A x i : ℝ)) w-4/((n : ℝ)-1)) : ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧ Matrix.IsHadamard (fun i j => (A (rows i) j : ℝ) : Matrix (Fin n) (Fin n) ℝ) := by sorry
theorem single_parity_collision_rounding {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 4<n) (hFour : n%4=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1) (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hParity : ∀ x y,0<w x → 0<w y → (∏ i,A x i)=(∏ i,A y i)) (hCert : ((n : ℝ)^2-16)*collision w>(n : ℝ)+signMomentError (fun x i => (A x i : ℝ)) w-16/((n : ℝ)-1)) : ∃ rows : Fin n ↪ α,(∀ i,0<w (rows i)) ∧ Matrix.IsHadamard (fun i j => (A (rows i) j : ℝ) : Matrix (Fin n) (Fin n) ℝ) := by sorry
theorem explicit_collision_gap {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 4≤n) (hEven : n%2=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1) (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hiso : ∀ i j,∑ x,w x*(A x i : ℝ)*(A x j : ℝ)=if i=j then 1 else 0) : let c2 := 1/(n : ℝ)-4/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-4)); (c2<collision w → HasSupportedHadamard A w) ∧ (¬(∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H) → collision w≤c2) ∧ (4<n → n%4=0 → (∀ x y,0<w x → 0<w y → (∏ i,A x i)=(∏ i,A y i)) → let c4 := 1/(n : ℝ)-16/((n : ℝ)*((n : ℝ)-1)*((n : ℝ)^2-16)); (c4<collision w → HasSupportedHadamard A w) ∧ (¬(∃ H : Matrix (Fin n) (Fin n) ℝ,Matrix.IsHadamard H) → collision w≤c4)) := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section
def collisionWindowDelta (n : ℝ) : ℝ := 4/((n-1)*(n^2-4))
def collisionEntropyWindow (n : ℝ) : ℝ := -Real.log (1-collisionWindowDelta n)
theorem collisionEntropyWindow_pos {n : ℝ} (hn : 4≤n) : 0<collisionEntropyWindow n := by sorry
theorem positive_entropy_window {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : 4≤n) (hEven : n%2=0) (A : α → Fin n → ℤ) (hA : ∀ x i,A x i=1 ∨ A x i= -1) (w : α → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1) (hiso : ∀ i j,∑ x,w x*(A x i : ℝ)*(A x j : ℝ)=if i=j then 1 else 0) (hEntropy : shannon w<Real.log (n : ℝ)+collisionEntropyWindow n) : 0<collisionEntropyWindow n ∧ HasSupportedHadamard A w := by sorry
theorem collisionEntropyWindow_nat_relative_limit : Tendsto (fun n : ℕ => collisionEntropyWindow n/(4/(n : ℝ)^3)) atTop (𝓝 1) := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Filter Set
open scoped Topology
noncomputable section
def cubeProbabilityFeasible {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  (∀ x,0≤w x) ∧ (∑ x,w x)=1 ∧
    (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧
    (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)
theorem finite_polytope_local_max_criterion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (S : Finset E) (w : E) (hw : w∈convexHull ℝ (S : Set E)) : (IsLocalMaxOn (fun x : E => ‖x‖^2) (convexHull ℝ (S : Set E)) w ↔ ∀ v∈convexHull ℝ (S : Set E),Inner.inner ℝ w v≤ Inner.inner ℝ w w ∧ (Inner.inner ℝ w w ≤ Inner.inner ℝ w v → v=w)) ∧ (IsLocalMaxOn (fun x : E => ‖x‖^2) (convexHull ℝ (S : Set E)) w → (∃ ε : ℝ,0<ε ∧ ∀ v∈convexHull ℝ (S : Set E),v≠w → ‖v-w‖<ε → ‖v‖^2<‖w‖^2) ∧ w∈(convexHull ℝ (S : Set E)).extremePoints ℝ) := by sorry
theorem uniform_cube_vertex_strict_local_collision {d : ℕ} (p : (Fin d → Bool) → ℝ) (hp : cubeProbabilityFeasible p) (hVertex : p∈Set.extremePoints ℝ {q | cubeProbabilityFeasible q}) (c : ℝ) (hc : 0<c) (hUniform : ∀ x,p x=0 ∨ p x=c) : IsLocalMaxOn collision {q | cubeProbabilityFeasible q} p ∧ ∃ ε : ℝ,0<ε ∧ ∀ q,cubeProbabilityFeasible q → q≠p → ‖q-p‖<ε → collision q<collision p := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section
theorem arbitrarily_poor_character_traps (s : ℕ) (hs : 2≤s) : Fintype.card (TrapCoordinate s)=2*2^s-1 ∧ 4∣(Fintype.card (TrapCoordinate s)+1) ∧ ∃ p : (TrapCoordinate s → Bool) → ℝ, observedFeasible p ∧ (activeSupport p).card=2^(2*s) ∧ (∀ x,p x=0 ∨ p x=1/(2 : ℝ)^(2*s)) ∧ p∈Set.extremePoints ℝ {q | observedFeasible q} ∧ IsLocalMaxOn collision {q | observedFeasible q} p ∧ (∀ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q → q≠p → ‖q-p‖<2/((2 : ℝ)^(2*s)*((2 : ℝ)^(2*s)+1)) → collision q<collision p) ∧ collision p=1/(2 : ℝ)^(2*s) ∧ (∃ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q ∧ collision q=1/(2*(2 : ℝ)^s)) ∧ (∀ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q → collision q≤1/(2*(2 : ℝ)^s)) ∧ collision p/(1/(2*(2 : ℝ)^s))=2/(2 : ℝ)^s := by sorry
theorem character_trap_relative_collision_limit : Tendsto (fun s : ℕ => 2/(2 : ℝ)^s) atTop (𝓝 0) := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section
def eightTrapMasks : Fin 7 → Finset (Fin 4) := ![{0},{1},{0,1},{2},{0,2},{3},{1,3}]
def eightTrapCode (u : Fin 4 → Bool) : Fin 7 → Bool := fun j => decide (walshChar (eightTrapMasks j) u= -1)
noncomputable def eightTrapLaw : (Fin 7 → Bool) → ℝ := pushLaw eightTrapCode (fun _ : Fin 4 → Bool => (1/16 : ℝ))
theorem order_eight_character_trap : (∀ j : Fin 7,(∑ i∈eightTrapMasks j,2^i.val)=(![1,2,3,4,5,8,10] : Fin 7 → ℕ) j) ∧ cubeProbabilityFeasible eightTrapLaw ∧ (activeSupport eightTrapLaw).card=16 ∧ (∀ x,eightTrapLaw x=0 ∨ eightTrapLaw x=(1/16 : ℝ)) ∧ collision eightTrapLaw=(1/16 : ℝ) ∧ eightTrapLaw∈Set.extremePoints ℝ {q | cubeProbabilityFeasible q} ∧ IsLocalMaxOn collision {q | cubeProbabilityFeasible q} eightTrapLaw ∧ (∀ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q → q≠eightTrapLaw → ‖q-eightTrapLaw‖<(1/136 : ℝ) → collision q<collision eightTrapLaw) ∧ (∃ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ)) ∧ (∀ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q → collision q≤(1/8 : ℝ)) := by sorry
theorem character_trap_global_path_barrier {s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (he : e.Nonempty) (path : ℝ → ((TrapCoordinate s → Bool) → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1)) (hStart : path 0=trapLaw e) (hEnd : collision (path 1)=1/(2*(2 : ℝ)^s)) (hFeasible : ∀ t∈Set.Icc (0 : ℝ) 1,observedFeasible (path t)) : ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤1/(2 : ℝ)^(2*s)- 1/(((2 : ℝ)^(2*s))^2*((2 : ℝ)^(2*s)+1)) := by sorry
theorem order_eight_global_path_barrier (path : ℝ → ((Fin 7 → Bool) → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1)) (hStart : path 0=eightTrapLaw) (hEnd : collision (path 1)=(1/8 : ℝ)) (hFeasible : ∀ t∈Set.Icc (0 : ℝ) 1,cubeProbabilityFeasible (path t)) : ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤(1/16 : ℝ)-1/4352 := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Filter
open scoped Topology
def fourTrapNegativeCount (x : Fin 4 → Bool) : Nat := (Finset.univ.filter (fun i => x i=true)).card
def fourTrapRationalWeights (x : Fin 4 → Bool) : ℚ := if fourTrapNegativeCount x=0 then 1/6 else if fourTrapNegativeCount x=2 ∨ fourTrapNegativeCount x=3 then 1/12 else 0
def fiveTrapNegativeCount (x : Fin 5 → Bool) : Nat := (Finset.univ.filter (fun i => x i=true)).card
def fiveTrapRationalWeights (x : Fin 5 → Bool) : ℚ := if fiveTrapNegativeCount x=0 then 1/6 else if fiveTrapNegativeCount x=3 then 1/12 else 0
noncomputable def fourBitTrapLaw (x : Fin 4 → Bool) : ℝ := (fourTrapRationalWeights x : ℝ)
noncomputable def fiveBitTrapLaw (x : Fin 5 → Bool) : ℝ := (fiveTrapRationalWeights x : ℝ)
theorem four_bit_nonglobal_trap : (∀ x : Fin 4 → Bool,fourBitTrapLaw x=if fourTrapNegativeCount x=0 then (1/6 : ℝ) else if fourTrapNegativeCount x=2 ∨ fourTrapNegativeCount x=3 then 1/12 else 0) ∧ cubeProbabilityFeasible fourBitTrapLaw ∧ collision fourBitTrapLaw=(7/72 : ℝ) ∧ IsLocalMaxOn collision {q | cubeProbabilityFeasible q} fourBitTrapLaw ∧ (∃ ε : ℝ,0<ε ∧ ∀ q : (Fin 4 → Bool) → ℝ,cubeProbabilityFeasible q → q≠fourBitTrapLaw → ‖q-fourBitTrapLaw‖<ε → collision q<collision fourBitTrapLaw) ∧ (∃ q : (Fin 4 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ) ∧ collision fourBitTrapLaw<collision q) := by sorry
theorem five_bit_nonglobal_trap : (∀ x : Fin 5 → Bool,fiveBitTrapLaw x=if fiveTrapNegativeCount x=0 then (1/6 : ℝ) else if fiveTrapNegativeCount x=3 then 1/12 else 0) ∧ cubeProbabilityFeasible fiveBitTrapLaw ∧ collision fiveBitTrapLaw=(7/72 : ℝ) ∧ IsLocalMaxOn collision {q | cubeProbabilityFeasible q} fiveBitTrapLaw ∧ (∃ ε : ℝ,0<ε ∧ ∀ q : (Fin 5 → Bool) → ℝ,cubeProbabilityFeasible q → q≠fiveBitTrapLaw → ‖q-fiveBitTrapLaw‖<ε → collision q<collision fiveBitTrapLaw) ∧ (∃ q : (Fin 5 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ) ∧ collision fiveBitTrapLaw<collision q) := by sorry
end EntropyDesigns
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section
def fourHighCharacter (i : Fin 5) (x : Fin 4 → Bool) : ℤ :=
  ∏ j : Fin 4, if j.val=i.val then 1 else bitSign (x j)
def fourTranslatedWeights (s x : Fin 4 → Bool) : ℚ :=
  fourTrapRationalWeights (fun i => xor (x i) (s i))
def fourUniformWeights (i : Fin 5) (b : Bool) (x : Fin 4 → Bool) : ℚ :=
  if fourHighCharacter i x=bitSign b then 1/8 else 0
noncomputable def fourTranslatedLaw (s : Fin 4 → Bool) (x : Fin 4 → Bool) : ℝ :=
  (fourTranslatedWeights s x : ℝ)
noncomputable def fourUniformLaw (i : Fin 5) (b : Bool) (x : Fin 4 → Bool) : ℝ :=
  (fourUniformWeights i b x : ℝ)
theorem four_bit_all_path_barrier (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (γ : ℝ → ((Fin 4 → Bool) → ℝ))
    (hc : ContinuousOn γ (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t))
    (hStart : γ 0=fourTranslatedLaw s) (hEnd : γ 1=fourUniformLaw i b) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ collision (γ t) ≤ 3/32 ∧
      (1/288:ℝ) ≤ collision (γ 0)-collision (γ t) := by sorry
theorem four_bit_barrier_sharpness (s : Fin 4 → Bool) (i : Fin 5) :
    ∃ (b : Bool) (γ : ℝ → ((Fin 4 → Bool) → ℝ)),
      fourHighCharacter i s=bitSign b ∧
      Continuous γ ∧ γ 0=fourTranslatedLaw s ∧ γ 1=fourUniformLaw i b ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t)) ∧
      (∀ t : ℝ, (3/32:ℝ) ≤ collision (γ t)) ∧
      collision (γ (1/4))=(3/32:ℝ) ∧
      collision (γ 0)-collision (γ (1/4))=(1/288:ℝ) := by sorry
theorem four_bit_no_monotone_escape (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (γ : ℝ → ((Fin 4 → Bool) → ℝ))
    (hc : ContinuousOn γ (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t))
    (hStart : γ 0=fourTranslatedLaw s) (hEnd : γ 1=fourUniformLaw i b) :
    ¬MonotoneOn (fun t => collision (γ t)) (Set.Icc 0 1) := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Set Filter
open scoped Topology
noncomputable section
def cubeProbabilityMomentMatrix (d : ℕ) : Matrix (Unit ⊕ (Fin d ⊕ (Fin d×Fin d))) (Fin d → Bool) ℝ :=
  Sum.elim (fun _ _ => 1)
    (Sum.elim (fun i x => (bitSign (x i) : ℝ))
      (fun ij x => (bitSign (x ij.1) : ℝ)*(bitSign (x ij.2) : ℝ)))
theorem four_bit_escape_exposed_edge (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    IsExposed ℝ {q : (Fin 4 → Bool) → ℝ | cubeProbabilityFeasible q}
      (segment ℝ (fourTranslatedLaw s) (fourUniformLaw i b)) ∧
    fourTranslatedLaw s≠fourUniformLaw i b := by sorry
theorem four_bit_escape_supported_kernel (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) (z : (Fin 4 → Bool) → ℝ) :
    ((cubeProbabilityMomentMatrix 4).mulVec z=0 ∧ (∑ x, z x)=0 ∧
      (∀ x, fourTranslatedLaw s x=0 → fourUniformLaw i b x=0 → z x=0)) ↔
    ∃ r : ℝ, z=r • (fourUniformLaw i b-fourTranslatedLaw s) := by sorry
theorem four_bit_escape_circuit (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    (cubeProbabilityMomentMatrix 4).mulVec (fourUniformLaw i b-fourTranslatedLaw s)=0 ∧
    (∑ x, (fourUniformLaw i b-fourTranslatedLaw s) x)=0 ∧
    (Finset.univ.filter (fun x => (fourUniformLaw i b-fourTranslatedLaw s) x≠0)).card=12 ∧
    ∀ z : (Fin 4 → Bool) → ℝ,
      (cubeProbabilityMomentMatrix 4).mulVec z=0 → (∑ x, z x)=0 →
      (∀ x, (fourUniformLaw i b-fourTranslatedLaw s) x=0 → z x=0) → z≠0 →
      ∃ r : ℝ, r≠0 ∧ z=r • (fourUniformLaw i b-fourTranslatedLaw s) := by sorry
theorem four_bit_exact_escape_rule (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → cubeProbabilityFeasible
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)) ∧
    (∀ t : ℝ, collision (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)=
      7/72-t/36+t^2/18) ∧
    collision (fourUniformLaw i b)-collision (fourTranslatedLaw s)=(1/36:ℝ) ∧
    (∀ t : ℝ, 0<t → t<1/2 → collision
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)<collision (fourTranslatedLaw s)) ∧
    collision (fun x => (1-(1/2:ℝ))*fourTranslatedLaw s x+(1/2:ℝ)*fourUniformLaw i b x)=7/72 ∧
    (∀ t : ℝ, (3/32:ℝ) ≤ collision
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)) ∧
    collision (fun x => (1-(1/4:ℝ))*fourTranslatedLaw s x+(1/4:ℝ)*fourUniformLaw i b x)=3/32 := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open Filter Set
open scoped Topology
noncomputable section
noncomputable def entropyTransitionPhi (α : ℝ) : ℝ :=
  (4/3:ℝ)^α+10*(2/3:ℝ)^α-8
noncomputable def finiteRenyi {ι : Type*} [Fintype ι] (α : ℝ) (p : ι → ℝ) : ℝ :=
  if α=1 then shannon p else Real.log (∑ x, (p x)^α)/(1-α)
noncomputable def fourWeightedEntropyValue (α : ℝ) : ℝ :=
  if α=1 then Real.log 12-Real.log 2/6 else (Real.log ((2:ℝ)^α+10)-α*Real.log 12)/(1-α)
def fourUniformFamily (q : (Fin 4 → Bool) → ℝ) : Prop :=
  ∃ (i : Fin 5) (b : Bool), q=fourUniformLaw i b
def fourWeightedFamily (q : (Fin 4 → Bool) → ℝ) : Prop :=
  ∃ s : Fin 4 → Bool, q=fourTranslatedLaw s
noncomputable def IsCubeRenyiGlobalMin (α : ℝ) (q : (Fin 4 → Bool) → ℝ) : Prop :=
  ∀ v : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible v → finiteRenyi α q ≤ finiteRenyi α v
noncomputable def IsStrictCubeRenyiLocalMin (r : ℝ) (p : (Fin 4 → Bool) → ℝ) : Prop :=
  IsLocalMinOn (finiteRenyi r) {q | cubeProbabilityFeasible q} p ∧
    ∃ ε : ℝ, 0<ε ∧ ∀ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q → q≠p →
      ‖q-p‖<ε → finiteRenyi r p<finiteRenyi r q
theorem four_bit_complete_entropy_diagram :
    ∃ τ : ℝ, 6<τ ∧ τ<7 ∧ entropyTransitionPhi τ=0 ∧
      (∀ β : ℝ, 1<β → entropyTransitionPhi β=0 → β=τ) ∧
      (∀ α : ℝ, 0<α → ∀ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q →
        (IsCubeRenyiGlobalMin α q ↔
          if α<τ then fourUniformFamily q else if τ<α then fourWeightedFamily q else
            fourUniformFamily q ∨ fourWeightedFamily q)) ∧
      (∀ α : ℝ, 0<α → ∃ q : (Fin 4 → Bool) → ℝ, cubeProbabilityFeasible q ∧
        finiteRenyi α q=min (Real.log 8) (fourWeightedEntropyValue α) ∧ IsCubeRenyiGlobalMin α q) ∧
      (∀ r : ℝ, 1<r →
        (∀ (i : Fin 5) (b : Bool), IsStrictCubeRenyiLocalMin r (fourUniformLaw i b)) ∧
        (∀ s : Fin 4 → Bool, IsStrictCubeRenyiLocalMin r (fourTranslatedLaw s))) ∧
      Tendsto (fun α : ℝ => (Real.log ((2:ℝ)^α+10)-α*Real.log 12)/(1-α))
        (𝓝[≠] (1:ℝ)) (𝓝 (Real.log 12-Real.log 2/6)) := by sorry
end
end EntropyDesigns
namespace EntropyDesigns
open scoped ComplexOrder
set_option autoImplicit false
noncomputable def stochasticProduct {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, ∑ j, B i j*x j
noncomputable def classicalStochasticCapacity {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ) : ℝ :=
  sInf (Set.range (fun x : {x : ι → ℝ // ∀ j, 0<x j} => stochasticProduct B x.val/(∏ j, x.val j)))
noncomputable def stochasticComplexChannel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => ∑ j, (B i j : ℂ)*X j j)
noncomputable def operatorStochasticCapacity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) : ℝ :=
  sInf (Set.range (fun X : {X : Matrix ι ι ℂ // X.PosDef} =>
    (stochasticComplexChannel B X.val).det.re/X.val.det.re))
noncomputable def stochasticKraus {ι : Type*} [DecidableEq ι]
    (B : Matrix ι ι ℝ) (i j : ι) : Matrix ι ι ℂ := Matrix.single i j (Real.sqrt (B i j) : ℂ)
theorem doubly_stochastic_capacities_are_blind {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j, 0≤B i j)
    (hRows : ∀ i, ∑ j, B i j=1) (hCols : ∀ j, ∑ i, B i j=1) :
    classicalStochasticCapacity B=1 ∧ operatorStochasticCapacity B=1 ∧
    stochasticComplexChannel B (1 : Matrix ι ι ℂ)=1 ∧
    stochasticComplexChannel B.transpose (1 : Matrix ι ι ℂ)=1 ∧
    (∀ X : Matrix ι ι ℂ, stochasticComplexChannel B X=
      ∑ i, ∑ j, stochasticKraus B i j*X*(stochasticKraus B i j).conjTranspose) ∧
    (∀ X Y : Matrix ι ι ℂ, Matrix.trace ((stochasticComplexChannel B X).conjTranspose*Y)=
      Matrix.trace (X.conjTranspose*stochasticComplexChannel B.transpose Y)) ∧
    (∀ k : ℕ, ∀ Y : Matrix (ι×Fin k) (ι×Fin k) ℂ, Y.PosSemidef →
      (∑ i, ∑ j,
        (Matrix.kronecker (stochasticKraus B i j) (1 : Matrix (Fin k) (Fin k) ℂ))*Y*
          (Matrix.kronecker (stochasticKraus B i j) (1 : Matrix (Fin k) (Fin k) ℂ)).conjTranspose).PosSemidef) ∧
    (∀ U : Matrix ι ι ℝ, U*U.transpose=1 → U.transpose*U=1 →
      classicalStochasticCapacity (fun i j => U i j^2)=1 ∧
      operatorStochasticCapacity (fun i j => U i j^2)=1 ∧
      stochasticComplexChannel (fun i j => U i j^2) (1 : Matrix ι ι ℂ)=1 ∧
      stochasticComplexChannel (fun i j => U j i^2) (1 : Matrix ι ι ℂ)=1) := by sorry
end EntropyDesigns
namespace EntropyDesigns
open scoped Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable def parityGapExact (N : ℝ) : ℝ :=
  (Real.sqrt (1+Real.sqrt (2*(N-2)/N))-1)^2/N
noncomputable def parityGapSimple (N : ℝ) : ℝ := 2*(N-2)/(9*N^2)
theorem elementary_orthogonal_parity_gap (n : ℕ) (hn : n%4=2)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U*U.transpose=1) (hUt : U.transpose*U=1) :
    parityGapExact (n:ℝ)≤(∑ i, ∑ j, U i j^4)-1 ∧
    parityGapSimple (n:ℝ)≤parityGapExact (n:ℝ) ∧
    ‖Matrix.of (fun i j : Fin n => U i j^2-1/(n:ℝ))‖^2=
      (∑ i, ∑ j, U i j^4)-1 := by sorry
theorem paley_second_finite_field_exists (F : Type*) [Field F] [Fintype F]
    (hres : Fintype.card F%4=1) :
    ∃ H : Matrix (Fin (2*(Fintype.card F+1))) (Fin (2*(Fintype.card F+1))) ℝ,
      Matrix.IsHadamard H := by sorry
theorem odd_prime_twice_successor_hadamard {p : ℕ} (hp : p.Prime) (hodd : p≠2) :
    ∃ H : Matrix (Fin (2*(p+1))) (Fin (2*(p+1))) ℝ,Matrix.IsHadamard H := by sorry
end EntropyDesigns
