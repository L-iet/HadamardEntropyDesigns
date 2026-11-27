/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.ExchangeableHierarchy
noncomputable section
open scoped BigOperators ComplexOrder

def tensorVector {A : Type*} (k : ℕ) (v : A → ℂ) (x : Fin k → A) : ℂ :=
  ∏ i, v (x i)

def pureTensor {A : Type*} (k : ℕ) (v : A → ℂ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  Matrix.vecMulVec (tensorVector k v) (star (tensorVector k v))

def traceFirst {A : Type*} [Fintype A] {k : ℕ}
    (M : Matrix (Fin (k+1) → A) (Fin (k+1) → A) ℂ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  fun x y => ∑ a, M (Fin.cons a x) (Fin.cons a y)

def uniformHierarchy {S A : Type*} [Fintype S] (v : S → A → ℂ) (k : ℕ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  (1/(Fintype.card S : ℝ)) • ∑ z, pureTensor k (v z)

theorem pureTensor_posSemidef {A : Type*} [Fintype A] (k : ℕ) (v : A → ℂ) :
    (pureTensor k v).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star (tensorVector k v)

theorem tensorVector_cons {A : Type*} (k : ℕ) (v : A → ℂ) (a : A) (x : Fin k → A) :
    tensorVector (k+1) v (Fin.cons a x)=v a*tensorVector k v x := by
  simp [tensorVector,Fin.prod_univ_succ]

theorem tensorVector_reindex {A : Type*} (k : ℕ) (v : A → ℂ)
    (π : Equiv.Perm (Fin k)) (x : Fin k → A) :
    tensorVector k v (x ∘ π)=tensorVector k v x :=
  Equiv.prod_comp π (fun i => v (x i))

theorem pureTensor_trace {A : Type*} [Fintype A] (k : ℕ) (v : A → ℂ)
    (hv : ∑ a,v a*star (v a)=1) : Matrix.trace (pureTensor k v)=1 := by
  classical
  change (∑ x : Fin k → A,tensorVector k v x*star (tensorVector k v x))=1
  simp only [tensorVector,star_prod,← Finset.prod_mul_distrib]
  have hf := Fintype.prod_sum (fun (_ : Fin k) (a : A) => v a*star (v a))
  rw [← hf]
  simp only [hv,Finset.prod_const_one]

theorem pureTensor_consistent {A : Type*} [Fintype A] (k : ℕ) (v : A → ℂ)
    (hv : ∑ a,v a*star (v a)=1) :
    traceFirst (pureTensor (k+1) v)=pureTensor k v := by
  classical
  ext x y
  change (∑ a,tensorVector (k+1) v (Fin.cons a x)*star (tensorVector (k+1) v (Fin.cons a y)))=
    tensorVector k v x*star (tensorVector k v y)
  simp only [tensorVector_cons,star_mul]
  have he (a : A) : (v a*tensorVector k v x)*(star (tensorVector k v y)*star (v a))=
      (v a*star (v a))*(tensorVector k v x*star (tensorVector k v y)) := by ring
  simp_rw [he]
  rw [← Finset.sum_mul,hv,one_mul]

theorem uniformHierarchy_posSemidef {S A : Type*} [Fintype S] [Fintype A]
    (v : S → A → ℂ) (k : ℕ) : (uniformHierarchy v k).PosSemidef := by
  apply (Matrix.posSemidef_sum Finset.univ (fun z _ => pureTensor_posSemidef k (v z))).smul
  exact one_div_nonneg.mpr (Nat.cast_nonneg _)

theorem uniformHierarchy_reindex {S A : Type*} [Fintype S] (v : S → A → ℂ)
    (k : ℕ) (π : Equiv.Perm (Fin k)) (x y : Fin k → A) :
    uniformHierarchy v k (x ∘ π) (y ∘ π)=uniformHierarchy v k x y := by
  classical
  simp only [uniformHierarchy,Matrix.smul_apply,Matrix.sum_apply,pureTensor,
    Matrix.vecMulVec_apply,Pi.star_apply,tensorVector_reindex]

theorem uniformHierarchy_trace {S A : Type*} [Fintype S] [Nonempty S] [Fintype A]
    (v : S → A → ℂ) (hv : ∀ z, ∑ a,v z a*star (v z a)=1) (k : ℕ) :
    Matrix.trace (uniformHierarchy v k)=1 := by
  classical
  have hn : (Fintype.card S : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [uniformHierarchy,Matrix.trace_smul,Matrix.trace_sum]
  simp only [pureTensor_trace k _ (hv _),Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one]
  change (((1/(Fintype.card S:ℝ)):ℝ):ℂ) * (((Fintype.card S:ℝ)):ℂ)=1
  rw [← Complex.ofReal_mul,div_mul_cancel₀ _ hn]
  rfl

theorem uniformHierarchy_consistent {S A : Type*} [Fintype S] [Fintype A]
    (v : S → A → ℂ) (hv : ∀ z, ∑ a,v z a*star (v z a)=1) (k : ℕ) :
    traceFirst (uniformHierarchy v (k+1))=uniformHierarchy v k := by
  classical
  ext x y
  simp only [traceFirst,uniformHierarchy,Matrix.smul_apply,Matrix.sum_apply]
  rw [← Finset.smul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact congrFun (congrFun (pureTensor_consistent k (v z) (hv z)) x) y

end
end EntropyDesigns.ExchangeableHierarchy
