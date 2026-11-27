/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [Fintype α]
def inner (v w : ι → ℝ) : ℝ := ∑ i,v i*w i
def outer (v w : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i*w j
def effect (a : ℝ) (v : ι → ℝ) : Matrix ι ι ℝ := a • outer v v
def frobeniusSq (A : Matrix ι ι ℝ) : ℝ := ∑ i,∑ j,(A i j)^2
def commutator (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ := A*B-B*A

def projectivityDefect (w : α → ℝ) (v : α → ι → ℝ) : ℝ :=
  ∑ a,Matrix.trace (effect (w a) (v a)-effect (w a) (v a)*effect (w a) (v a))
def commutatorEnergy (w : α → ℝ) (v : α → ι → ℝ) : ℝ :=
  ∑ a,∑ b,frobeniusSq (commutator (effect (w a) (v a)) (effect (w b) (v b)))

def tensorWeight (w : α → ℝ) (r : ℕ) (a : Fin r → α) : ℝ := ∏ t,w (a t)
def tensorVector (v : α → ι → ℝ) (r : ℕ) (a : Fin r → α) (i : Fin r → ι) : ℝ :=
  ∏ t,v (a t) (i t)


end
noncomputable section
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
def UniformHadamardMeasurement (w : α → ℝ) (v : α → ι → ℝ) : Prop :=
  ∃ e : α ≃ ι,Matrix.IsHadamard (fun i j => v (e.symm i) j) ∧
    ∀ a,w a=1/(Fintype.card ι:ℝ)

def euclideanOperatorNorm (A : Matrix ι ι ℝ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜:=ℝ) A‖

theorem uniform_tight_povm_operator_bounds (o : ι) (v : α → ι → ℝ)
    (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (htight : ∑ a,effect (1/(Fintype.card α:ℝ)) (v a)=(1 : Matrix ι ι ℝ)) :
    let N := (Fintype.card ι:ℝ)
    let M := (Fintype.card α:ℝ)
    (∀ a,euclideanOperatorNorm (effect (1/M) (v a)-effect (1/M) (v a)*effect (1/M) (v a))=
      (N/M)*(1-N/M)) ∧
    (IsGreatest (Set.range (fun a => euclideanOperatorNorm
      (effect (1/M) (v a)-effect (1/M) (v a)*effect (1/M) (v a)))) ((N/M)*(1-N/M))) ∧
    (∀ a b,(euclideanOperatorNorm (commutator (effect (1/M) (v a)) (effect (1/M) (v b))))^2≤
      (N/M)^3*(1-N/M)) ∧
    (commutatorEnergy (fun _ : α => 1/M) v/N≤2*(N/M)^2*(1-N/M)) := by sorry

theorem actual_tensor_povm_no_activation (o : ι) (w : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a,0<w a) (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (hinj : Function.Injective v)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) (r : ℕ) (hr : r≠0) :
    (∑ a,effect (tensorWeight w r a) (tensorVector v r a)=
      (1 : Matrix (Fin r → ι) (Fin r → ι) ℝ)) ∧
    (projectivityDefect (tensorWeight w r) (tensorVector v r)/(Fintype.card ι:ℝ)^r=
      1-((Fintype.card ι:ℝ)*(∑ a,(w a)^2))^r) ∧
    ((∀ a,effect (tensorWeight w r a) (tensorVector v r a)*effect (tensorWeight w r a) (tensorVector v r a)=
      effect (tensorWeight w r a) (tensorVector v r a)) ↔ UniformHadamardMeasurement w v) ∧
    ((∀ a b,effect (tensorWeight w r a) (tensorVector v r a)*effect (tensorWeight w r b) (tensorVector v r b)=
      effect (tensorWeight w r b) (tensorVector v r b)*effect (tensorWeight w r a) (tensorVector v r a)) ↔
      UniformHadamardMeasurement w v) := by sorry

end
end EntropyDesigns.Quantum
