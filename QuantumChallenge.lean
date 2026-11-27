/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
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

end
noncomputable section
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
def UniformHadamardMeasurement (w : α → ℝ) (v : α → ι → ℝ) : Prop :=
  ∃ e : α ≃ ι,Matrix.IsHadamard (fun i j => v (e.symm i) j) ∧
    ∀ a,w a=1/(Fintype.card ι:ℝ)

theorem exact_projective_commuting_criteria (o : ι) (w : α → ℝ) (v : α → ι → ℝ)
    (hw : ∀ a,0<w a) (hv : ∀ a,v a o=1) (hsign : ∀ a i,v a i=1 ∨ v a i= -1)
    (hinj : Function.Injective v)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) :
    (UniformHadamardMeasurement w v ↔ ∀ a,effect (w a) (v a)*effect (w a) (v a)=effect (w a) (v a)) ∧
    (UniformHadamardMeasurement w v ↔ ∀ a b,effect (w a) (v a)*effect (w b) (v b)=effect (w b) (v b)*effect (w a) (v a)) ∧
    (UniformHadamardMeasurement w v ↔ commutatorEnergy w v=0) := by sorry

omit [DecidableEq ι] [DecidableEq α] in
theorem exact_projectivity_defect (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hmass : ∑ a,w a=1) (hnorm : ∀ a,inner (v a) (v a)=N) :
    projectivityDefect w v=N-N^2*(∑ a,(w a)^2) := by sorry

omit [DecidableEq ι] [DecidableEq α] in
theorem exact_ordered_commutator_energy (w : α → ℝ) (v : α → ι → ℝ)
    (N : ℝ) (hnorm : ∀ a,inner (v a) (v a)=N) :
    (commutatorEnergy w v=2*∑ a,∑ b,(w a)^2*(w b)^2*(inner (v a) (v b))^2*
      (N^2-(inner (v a) (v b))^2)) ∧
    (commutatorEnergy w v=2*(
      Matrix.trace ((∑ a,effect (w a) (v a)*effect (w a) (v a))*
        (∑ a,effect (w a) (v a)*effect (w a) (v a)))-
      ∑ a,∑ b,(Matrix.trace (effect (w a) (v a)*effect (w b) (v b)))^2)) := by sorry
end
end EntropyDesigns.Quantum
