/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
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
namespace Concentration
open SupportFace

def observedAtoms {k s : ℕ} {i0 : Fin k} (p : SourceOutcome k s i0 → ℝ) :
    Finset (SourceOutcome k s i0) := Finset.univ.filter (fun y => p y≠0)

namespace Interpolation
def outsideLawMass {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (q : α → ℝ) : ℝ :=
  ∑ x∈Sᶜ,q x

end Interpolation
open Interpolation

theorem face_optimum_barrier_bound {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) :
    ‖q-p‖≤outsideLawMass (observedAtoms p) q ∧
      collision q-1/((2:ℝ)^s)^2≤
        -2*outsideLawMass (observedAtoms p) q/((2:ℝ)^s)^2+
          (((2:ℝ)^s)^2+1)*(outsideLawMass (observedAtoms p) q)^2 := by sorry

theorem face_optimum_strict_local_collision {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2) :
    0<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) ∧
      ∀ q : SourceOutcome k s i0 → ℝ,sourceFeasible i0 q → q≠p →
        ‖q-p‖<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1)) → collision q<collision p := by sorry

theorem face_optimum_small_outside_collision {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q)
    (hb : 0<outsideLawMass (observedAtoms p) q)
    (hsmall : outsideLawMass (observedAtoms p) q<2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1))) :
    collision q<collision p := by sorry

theorem face_optimum_better_requires_outside_mass {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s))
    (i0 : Fin k) (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p)
    (hsupport : sourceSupported e i0 p) (hcollision : collision p=1/((2:ℝ)^s)^2)
    (q : SourceOutcome k s i0 → ℝ) (hq : sourceFeasible i0 q) (hbetter : collision p<collision q) :
    2/(((2:ℝ)^s)^2*(((2:ℝ)^s)^2+1))≤outsideLawMass (observedAtoms p) q := by sorry

theorem face_optimum_path_barrier {k s : ℕ} (hk : 2≤k) (e : Finset (Fin s)) (i0 : Fin k)
    (p : SourceOutcome k s i0 → ℝ) (hp : sourceFeasible i0 p) (hsupport : sourceSupported e i0 p)
    (hcollision : collision p=1/((2:ℝ)^s)^2)
    (path : ℝ → (SourceOutcome k s i0 → ℝ)) (hcont : ContinuousOn path (Set.Icc 0 1))
    (hstart : path 0=p) (hend : collision p<collision (path 1))
    (hlaw : ∀ t∈Set.Icc (0:ℝ) 1,sourceFeasible i0 (path t)) :
    ∃ t∈Set.Icc (0:ℝ) 1,collision (path t)≤
      1/((2:ℝ)^s)^2-1/((((2:ℝ)^s)^2)^2*(((2:ℝ)^s)^2+1)) := by sorry

end Concentration
end
end EntropyDesigns
