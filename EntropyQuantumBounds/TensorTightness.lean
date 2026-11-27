/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantumBounds.TensorWeights
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

theorem tensor_tight (w : α → ℝ) (v : α → ι → ℝ) (r : ℕ)
    (htight : ∑ a,effect (w a) (v a)=(1 : Matrix ι ι ℝ)) :
    ∑ a,effect (tensorWeight w r a) (tensorVector v r a)=
      (1 : Matrix (Fin r → ι) (Fin r → ι) ℝ) := by
  have hentry (i j : ι) : (∑ a,w a*v a i*v a j)=if i=j then 1 else 0 := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M i j) htight
    simpa [Matrix.sum_apply,Matrix.one_apply,effect,outer,mul_assoc] using h
  ext i j
  simp only [Matrix.sum_apply,effect,Matrix.smul_apply,smul_eq_mul,outer,tensorWeight,tensorVector]
  calc
    _=∑ a : Fin r → α,∏ t,w (a t)*v (a t) (i t)*v (a t) (j t) := by
      simp only [Finset.prod_mul_distrib,mul_assoc]
    _=∏ t,∑ a,w a*v a (i t)*v a (j t) :=
      (Fintype.prod_sum (fun t a => w a*v a (i t)*v a (j t))).symm
    _=∏ t,if i t=j t then (1:ℝ) else 0 := by simp only [hentry]
    _=(1 : Matrix (Fin r → ι) (Fin r → ι) ℝ) i j := by
      by_cases hij : i=j
      · subst j;simp
      · obtain ⟨t,ht⟩ : ∃ t,i t≠j t := Function.ne_iff.mp hij
        have hz : (∏ t,if i t=j t then (1:ℝ) else 0)=0 :=
          Finset.prod_eq_zero (Finset.mem_univ t) (by simp [ht])
        simpa [hij] using hz

theorem tensor_single_coordinate (o : ι) (v : α → ι → ℝ) (r : ℕ)
    (hv : ∀ a,v a o=1) (a : Fin r → α) (t : Fin r) (j : ι) :
    tensorVector v r a (Function.update (fun _ => o) t j)=v (a t) j := by
  unfold tensorVector
  rw [Finset.prod_eq_single t]
  · simp
  · intro s _ hst
    simp [Function.update_of_ne hst,hv]
  · simp

theorem tensor_vector_injective (o : ι) (v : α → ι → ℝ) (r : ℕ)
    (hv : ∀ a,v a o=1) (hinj : Function.Injective v) :
    Function.Injective (tensorVector v r) := by
  intro a b hab
  funext t
  apply hinj
  funext j
  have h := congrArg (fun f : (Fin r → ι) → ℝ => f (Function.update (fun _ => o) t j)) hab
  simpa only [tensor_single_coordinate o v r hv] using h

theorem tensor_sign (v : α → ι → ℝ) (r : ℕ)
    (hsign : ∀ a i,v a i=1 ∨ v a i= -1) :
    ∀ a i,tensorVector v r a i=1 ∨ tensorVector v r a i= -1 := by
  intro a i
  apply sq_eq_one_iff.mp
  have hs (t : Fin r) : (v (a t) (i t))^2=1 := by
    rcases hsign (a t) (i t) with h|h <;> rw [h] <;> ring
  simp [tensorVector,← Finset.prod_pow,hs]
end
end EntropyDesigns.Quantum
