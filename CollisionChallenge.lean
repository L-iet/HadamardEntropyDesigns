/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Basic
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators
def bitSign (b : Bool) : ℤ := if b then -1 else 1
def collision {α : Type*} [Fintype α] (w : α → ℝ) : ℝ := ∑ a,w a^2
def roundedDimension (n : ℕ) : ℕ := 4*((n+3)/4)
namespace SymmetricEntropy
def CoordinatePermutationInvariant {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  ∀ σ : Equiv.Perm (Fin d),∀ x : Fin d → Bool,w (fun i => x (σ i))=w x
def IsSymmetricPairwiseLaw {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  (∀ x,0≤w x) ∧ (∑ x,w x=1) ∧ CoordinatePermutationInvariant w ∧
    (∀ i,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
    (∀ i j,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0)
def maximumSymmetricCollision (d : ℕ) : ℝ :=
  sSup {c : ℝ | ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧ collision w=c}

theorem symmetric_collision_upper {d : ℕ} (hd : 7≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w≤1/(d:ℝ)^2+(d:ℝ)/((d:ℝ)-2)^4+2/((d:ℝ)*((d:ℝ)-1)) := by sorry

theorem collision_envelope_strict {x : ℝ} (hx : 7≤x) :
    1/x^2+x/(x-2)^4+2/(x*(x-1))<4/x^2 := by sorry

theorem maximumSymmetricCollision_spec (d : ℕ) (hd : 2≤d) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧ collision w=maximumSymmetricCollision d ∧
      ∀ v : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw v → collision v≤maximumSymmetricCollision d := by sorry

theorem maximumSymmetricCollision_theta :
    Asymptotics.IsTheta Filter.atTop maximumSymmetricCollision (fun d : ℕ => 1/(d:ℝ)^2) := by sorry

theorem symmetric_no_attainment {d : ℕ} (hd : 5≤d)
    (w : (Fin d → Bool) → ℝ) (hw : ∀ x,0≤w x) (hmass : ∑ x,w x=1)
    (hsym : CoordinatePermutationInvariant w)
    (hmean : ∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0)
    (hpair : ∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0) :
    collision w≠1/(roundedDimension (d+1):ℝ) := by sorry

theorem exists_matching_symmetric_law (d : ℕ) (hd : 2≤d) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧ 1/(4*(d:ℝ)^2)≤collision w := by sorry

theorem small_symmetric_attainment (d : ℕ) (hd : 2≤d) (hd4 : d≤4) :
    ∃ w : (Fin d → Bool) → ℝ,IsSymmetricPairwiseLaw w ∧
      collision w=1/(roundedDimension (d+1):ℝ) := by sorry

end SymmetricEntropy
end
end EntropyDesigns
