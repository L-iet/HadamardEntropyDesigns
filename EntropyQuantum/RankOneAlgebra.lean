/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
def inner (v w : ι → ℝ) : ℝ := ∑ i,v i*w i
def outer (v w : ι → ℝ) : Matrix ι ι ℝ := fun i j => v i*w j
def effect (a : ℝ) (v : ι → ℝ) : Matrix ι ι ℝ := a • outer v v
def frobeniusSq (A : Matrix ι ι ℝ) : ℝ := ∑ i,∑ j,(A i j)^2
def commutator (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ := A*B-B*A

theorem inner_comm (v w : ι → ℝ) : inner v w=inner w v := by
  simp only [inner,mul_comm]

theorem outer_mul (v w x y : ι → ℝ) : outer v w*outer x y=inner w x • outer v y := by
  ext i j
  change (∑ k,(v i*w k)*(x k*y j))=(∑ k,w k*x k)*(v i*y j)
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem trace_outer (v w : ι → ℝ) : Matrix.trace (outer v w)=inner v w := rfl

theorem effect_square (a : ℝ) (v : ι → ℝ) :
    effect a v*effect a v=(a^2*inner v v) • outer v v := by
  rw [effect,Matrix.smul_mul,Matrix.mul_smul,outer_mul]
  simp only [smul_smul]
  congr 1
  ring

theorem effect_trace (a : ℝ) (v : ι → ℝ) : Matrix.trace (effect a v)=a*inner v v := by
  simp [effect,Matrix.trace_smul,trace_outer]

theorem effect_square_trace (a : ℝ) (v : ι → ℝ) :
    Matrix.trace (effect a v*effect a v)=a^2*(inner v v)^2 := by
  rw [effect_square,Matrix.trace_smul,trace_outer]
  simp only [smul_eq_mul]
  ring

theorem effect_commutator (a b : ℝ) (v w : ι → ℝ) :
    commutator (effect a v) (effect b w)=
      (a*b*inner v w) • (outer v w-outer w v) := by
  unfold commutator effect
  rw [Matrix.smul_mul,Matrix.mul_smul,outer_mul,Matrix.smul_mul,Matrix.mul_smul,outer_mul]
  rw [inner_comm w v]
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring
theorem frobeniusSq_smul (a : ℝ) (A : Matrix ι ι ℝ) :
    frobeniusSq (a • A)=a^2*frobeniusSq A := by
  simp [frobeniusSq,Matrix.smul_apply,mul_pow,← Finset.mul_sum]

theorem wedge_frobenius (v w : ι → ℝ) :
    frobeniusSq (outer v w-outer w v)=
      2*(inner v v*inner w w-(inner v w)^2) := by
  have hp (i j : ι) : (v i*w j-w i*v j)^2=
      v i^2*w j^2+w i^2*v j^2-2*(v i*w i)*(v j*w j) := by ring
  simp only [frobeniusSq,Matrix.sub_apply,outer,hp]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [← Finset.sum_mul]
  simp only [inner,pow_two]
  ring_nf
  simp only [← Finset.sum_mul]
  ring

theorem commutator_frobenius (a b : ℝ) (v w : ι → ℝ) :
    frobeniusSq (commutator (effect a v) (effect b w))=
      2*a^2*b^2*(inner v w)^2*(inner v v*inner w w-(inner v w)^2) := by
  rw [effect_commutator,frobeniusSq_smul,wedge_frobenius]
  ring
end
end EntropyDesigns.Quantum
