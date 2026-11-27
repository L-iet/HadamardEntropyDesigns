/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
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

theorem card_source_coordinates {k : ℕ} (s : ℕ) (i0 : Fin k) :
    Fintype.card (SourceCoordinate k s i0)=k*(2^s)-1 := by sorry

theorem source_collision_upper {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hsupport : sourceSupported e i0 q) :
    (∀ y,q y≤1/((2:ℝ)^s)^2) ∧ collision q≤1/((2:ℝ)^s)^2 := by sorry

theorem source_collision_equality_oa {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hsupport : sourceSupported e i0 q)
    (heq : collision q=1/((2:ℝ)^s)^2) :
    (∀ y,q y=0 ∨ q y=1/((2:ℝ)^s)^2) ∧
    Nat.card {y : SourceOutcome k s i0 // q y≠0}=(2^s)^2 ∧
    (∀ i j : Fin k,i≠j → Function.Bijective
      (fun x : {x : BlockSeeds k s // sourcePullback e i0 q x≠0} => (x.val i,x.val j))) := by sorry

theorem source_attaining_law {k s : ℕ} (hk : 2≤k) (hkh : k≤2^s)
    (e : Finset (Fin s)) (he : e.Nonempty) (i0 : Fin k) :
    ∃ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q ∧ sourceSupported e i0 q ∧
      collision q=1/((2:ℝ)^s)^2 ∧
      (∀ y,q y=0 ∨ q y=1/((2:ℝ)^s)^2) ∧
      Nat.card {y : SourceOutcome k s i0 // q y≠0}=(2^s)^2 := by sorry
end SupportFace
end
end EntropyDesigns
