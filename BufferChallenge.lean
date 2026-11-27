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
@[expose] public section
namespace EntropyDesigns
def collision {α : Type*} [Fintype α] (w : α → ℝ) : ℝ :=
  ∑ a, w a ^ 2

def bitSign (b : Bool) : ℤ := if b then -1 else 1

noncomputable def uniformOn {α : Type*} [DecidableEq α] (G : Finset α) (N : ℕ) (a : α) : ℝ :=
  if a ∈ G then 1 / (N : ℝ) else 0

def walshChar {d : ℕ} (S : Finset (Fin d)) (x : Fin d → Bool) : ℤ :=
  ∏ i ∈ S, bitSign (x i)

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

theorem sparse_uniform_affine_buffer_obstruction {d : ℕ} (hd : 16≤d)
    (hres : (d+4)%4=0) (G : Finset (Fin d → Bool)) (hcard : G.card=d+4) :
    let w := uniformOn G (d+4)
    let K : ℝ := (d:ℝ)*((d:ℝ)+1)/2
    ((∀ i : LowIndex d,fourierCoefficient w lowCharacter i=0) ↔
      (∀ i : Fin d,∑ x,w x*(bitSign (x i):ℝ)=0) ∧
      (∀ i j : Fin d,i≠j → ∑ x,w x*(bitSign (x i):ℝ)*(bitSign (x j):ℝ)=0)) ∧
    ((∀ i : LowIndex d,fourierCoefficient w lowCharacter i=0) →
      ∃ H : Matrix (Fin (d+4)) (Fin (d+4)) ℝ,Matrix.IsHadamard H) ∧
    ((∃ i : LowIndex d,fourierCoefficient w lowCharacter i≠0) →
      ∀ B : ℝ,0≤B →
        (∀ x,0≤affineCorrection w (lowPolynomial w) ((2:ℝ)^d) B x) →
        1/(2*((d:ℝ)+4)*Real.sqrt K)≤B ∧
        1/(8*((d:ℝ)+4)^2*Real.sqrt K)≤
          1/((d:ℝ)+4)-collision (affineCorrection w (lowPolynomial w) ((2:ℝ)^d) B) ∧
        1/(8*((d:ℝ)+4)^3)<1/(8*((d:ℝ)+4)^2*Real.sqrt K) ∧
        1/(1024*((d:ℝ)+4)^4)<1/(8*((d:ℝ)+4)^3)) := by sorry
end EntropyDesigns
