/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.RankOneAlgebra
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [Fintype α]
def tensorWeight (w : α → ℝ) (r : ℕ) (a : Fin r → α) : ℝ := ∏ t,w (a t)
def tensorVector (v : α → ι → ℝ) (r : ℕ) (a : Fin r → α) (i : Fin r → ι) : ℝ :=
  ∏ t,v (a t) (i t)

theorem tensor_weight_mass (w : α → ℝ) (r : ℕ) :
    (∑ a,tensorWeight w r a)=(∑ a,w a)^r := by
  exact (Fintype.sum_pow w r).symm

theorem tensor_weight_collision (w : α → ℝ) (r : ℕ) :
    (∑ a,(tensorWeight w r a)^2)=(∑ a,(w a)^2)^r := by
  simp only [tensorWeight,← Finset.prod_pow]
  exact (Fintype.sum_pow (fun a => (w a)^2) r).symm

theorem tensor_vector_inner (v : α → ι → ℝ) (r : ℕ) (a b : Fin r → α) :
    inner (tensorVector v r a) (tensorVector v r b)=∏ t,inner (v (a t)) (v (b t)) := by
  simp only [inner,tensorVector,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t i => v (a t) i*v (b t) i)).symm

theorem tensor_vector_norm (v : α → ι → ℝ) (r : ℕ) (N : ℝ)
    (hnorm : ∀ a,inner (v a) (v a)=N) (a : Fin r → α) :
    inner (tensorVector v r a) (tensorVector v r a)=N^r := by
  rw [tensor_vector_inner]
  simp [hnorm]

theorem tensor_weight_positive (w : α → ℝ) (r : ℕ) (hw : ∀ a,0<w a) :
    ∀ a,0<tensorWeight w r a := by
  intro a
  exact Finset.prod_pos (fun t _ => hw (a t))

theorem tensor_normalized (o : ι) (v : α → ι → ℝ) (r : ℕ)
    (hv : ∀ a,v a o=1) : ∀ a,tensorVector v r a (fun _ => o)=1 := by
  intro a
  simp [tensorVector,hv]
end
end EntropyDesigns.Quantum
