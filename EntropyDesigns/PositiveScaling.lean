/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Positivity
@[expose] public section
namespace EntropyDesigns
open scoped Matrix

theorem log_scaling_gap_nonneg {x : ℝ} (hx : 0<x) : 0 ≤ (x-1)*Real.log x := by
  by_cases h : 1≤x
  · exact mul_nonneg (by linarith) (Real.log_nonneg h)
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (Real.log_nonpos hx.le (by linarith))

theorem log_scaling_gap_eq_zero {x : ℝ} (hx : 0<x) (h : (x-1)*Real.log x=0) : x=1 := by
  rcases mul_eq_zero.mp h with h|h
  · linarith
  · rcases Real.log_eq_zero.mp h with h|h|h <;> linarith

theorem balanced_positive_scaling_unique {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → κ → ℝ) (q : ι → ℝ) (r : κ → ℝ)
    (hP : ∀ i j,0≤P i j) (hq : ∀ i,0<q i) (hr : ∀ j,0<r j)
    (hrows : ∀ i,∑ j,P i j=1) (hcols : ∀ j,∑ i,P i j=1)
    (hsrows : ∀ i,∑ j,q i*r j*P i j=1) (hscols : ∀ j,∑ i,q i*r j*P i j=1) :
    ∀ i j,q i*r j*P i j=P i j := by
  have hgap (i : ι) (j : κ) : 0≤P i j*((q i*r j-1)*Real.log (q i*r j)) :=
    mul_nonneg (hP i j) (log_scaling_gap_nonneg (mul_pos (hq i) (hr j)))
  have hsum : (∑ i,∑ j,P i j*((q i*r j-1)*Real.log (q i*r j)))=0 := by
    have ht (i : ι) (j : κ) :
        P i j*((q i*r j-1)*Real.log (q i*r j))=
          Real.log (q i)*(q i*r j*P i j-P i j)+
          Real.log (r j)*(q i*r j*P i j-P i j) := by
      rw [Real.log_mul (hq i).ne' (hr j).ne']
      ring
    simp_rw [ht]
    simp_rw [Finset.sum_add_distrib]
    have hfirst : (∑ i,∑ j,Real.log (q i)*(q i*r j*P i j-P i j))=0 := by
      simp_rw [← Finset.mul_sum,Finset.sum_sub_distrib,hsrows,hrows]
      simp
    have hsecond : (∑ i,∑ j,Real.log (r j)*(q i*r j*P i j-P i j))=0 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum,Finset.sum_sub_distrib,hscols,hcols]
      simp
    rw [hfirst,hsecond]
    norm_num
  intro i j
  have hrowzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hgap i j))).mp hsum i (Finset.mem_univ i)
  have hentry := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hgap i j)).mp hrowzero j (Finset.mem_univ j)
  by_cases hz : P i j=0
  · simp [hz]
  · have he := (mul_eq_zero.mp hentry).resolve_left hz
    rw [log_scaling_gap_eq_zero (mul_pos (hq i) (hr j)) he,one_mul]

def positiveDiagonalScale {ι : Type*} (U : Matrix ι ι ℝ) (d e : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => d i*U i j*e j

theorem orthogonal_diagonal_square_rows {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (h : U*Uᵀ=1) (i : ι) : (∑ j,U i j^2)=1 := by
  have hh := congrArg (fun M : Matrix ι ι ℝ => M i i) h
  simpa [Matrix.mul_apply,Matrix.transpose_apply,pow_two] using hh

theorem orthogonal_diagonal_square_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (h : Uᵀ*U=1) (j : ι) : (∑ i,U i j^2)=1 := by
  have hh := congrArg (fun M : Matrix ι ι ℝ => M j j) h
  simpa [Matrix.mul_apply,Matrix.transpose_apply,pow_two] using hh

theorem positive_diagonal_orthogonal_rigidity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (d e : ι → ℝ) (hd : ∀ i,0<d i) (he : ∀ i,0<e i)
    (hUrow : U*Uᵀ=1) (hUcol : Uᵀ*U=1)
    (hZrow : positiveDiagonalScale U d e*(positiveDiagonalScale U d e)ᵀ=1)
    (hZcol : (positiveDiagonalScale U d e)ᵀ*positiveDiagonalScale U d e=1) :
    positiveDiagonalScale U d e=U := by
  have hrows (i : ι) : (∑ j,d i^2*e j^2*U i j^2)=1 := by
    convert orthogonal_diagonal_square_rows _ hZrow i using 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [positiveDiagonalScale]
    ring
  have hcols (j : ι) : (∑ i,d i^2*e j^2*U i j^2)=1 := by
    convert orthogonal_diagonal_square_columns _ hZcol j using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [positiveDiagonalScale]
    ring
  have hscale := balanced_positive_scaling_unique (fun i j => U i j^2) (fun i => d i^2) (fun j => e j^2)
    (fun i j => sq_nonneg _) (fun i => sq_pos_of_pos (hd i)) (fun j => sq_pos_of_pos (he j))
    (orthogonal_diagonal_square_rows U hUrow) (orthogonal_diagonal_square_columns U hUcol) hrows hcols
  ext i j
  by_cases hz : U i j=0
  · simp [positiveDiagonalScale,hz]
  · have hh := hscale i j
    have hfactor : (d i*e j)^2=1 := by
      have hm : (d i*e j)^2*(U i j)^2=1*(U i j)^2 := by nlinarith [hh]
      exact mul_right_cancel₀ (pow_ne_zero 2 hz) hm
    have hp : 0<d i*e j := mul_pos (hd i) (he j)
    have hprod : d i*e j=1 := by nlinarith
    change d i*U i j*e j=U i j
    calc
      _ = (d i*e j)*U i j := by ring
      _ = _ := by rw [hprod,one_mul]

def bipartiteSupportEdge {ι : Type*} (U : Matrix ι ι ℝ) : (ι ⊕ ι) → (ι ⊕ ι) → Prop
  | Sum.inl i, Sum.inr j => U i j ≠ 0
  | Sum.inr j, Sum.inl i => U i j ≠ 0
  | _, _ => False

def BipartiteSupportConnected {ι : Type*} (U : Matrix ι ι ℝ) : Prop :=
  ∀ v w,Relation.ReflTransGen (bipartiteSupportEdge U) v w

noncomputable def scalingVertex {ι : Type*} (d e : ι → ℝ) : (ι ⊕ ι) → ℝ :=
  Sum.elim d (fun j => (e j)⁻¹)

theorem connected_positive_diagonal_scales {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (d e : ι → ℝ) (hd : ∀ i,0<d i) (he : ∀ i,0<e i)
    (hUrow : U*Uᵀ=1) (hUcol : Uᵀ*U=1)
    (hZrow : positiveDiagonalScale U d e*(positiveDiagonalScale U d e)ᵀ=1)
    (hZcol : (positiveDiagonalScale U d e)ᵀ*positiveDiagonalScale U d e=1)
    (hconn : BipartiteSupportConnected U) :
    ∃ c : ℝ,0<c ∧ (∀ i,d i=c) ∧ ∀ j,e j=c⁻¹ := by
  classical
  have hrigid := positive_diagonal_orthogonal_rigidity U d e hd he hUrow hUcol hZrow hZcol
  have hedge (i j : ι) (hij : U i j ≠ 0) : d i=(e j)⁻¹ := by
    have hh := congrArg (fun M : Matrix ι ι ℝ => M i j) hrigid
    change d i*U i j*e j=U i j at hh
    have hm : (d i*e j)*U i j=1*U i j := by nlinarith [hh]
    have hde : d i*e j=1 := mul_right_cancel₀ hij hm
    calc
      d i = d i*(e j*(e j)⁻¹) := by rw [mul_inv_cancel₀ (he j).ne',mul_one]
      _ = (d i*e j)*(e j)⁻¹ := by ring
      _ = _ := by rw [hde,one_mul]
  have hstep (v w : ι ⊕ ι) (h : bipartiteSupportEdge U v w) : scalingVertex d e v=scalingVertex d e w := by
    cases v with
    | inl i =>
      cases w with
      | inl j => exact False.elim h
      | inr j => exact hedge i j h
    | inr j =>
      cases w with
      | inl i => exact (hedge i j h).symm
      | inr i => exact False.elim h
  have hpath (v w : ι ⊕ ι) : scalingVertex d e v=scalingVertex d e w := by
    have hh := hconn v w
    induction hh with
    | refl => rfl
    | @tail w z _ hstep' ih => exact ih.trans (hstep w z hstep')
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    letI := hi
    exact ⟨1,by norm_num,fun i => isEmptyElim i,fun i => isEmptyElim i⟩
  | inr hi =>
    letI := hi
    let i₀ : ι := Classical.choice hi
    refine ⟨d i₀,hd i₀,fun i => hpath (Sum.inl i) (Sum.inl i₀),?_⟩
    intro j
    have hh : (e j)⁻¹=d i₀ := hpath (Sum.inr j) (Sum.inl i₀)
    have hh' := congrArg (fun x : ℝ => x⁻¹) hh
    simpa only [inv_inv] using hh'

theorem positive_diagonal_balancing_rigidity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℝ) (d e : ι → ℝ) (hd : ∀ i,0<d i) (he : ∀ i,0<e i)
    (hUrow : U*Uᵀ=1) (hUcol : Uᵀ*U=1)
    (hZrow : positiveDiagonalScale U d e*(positiveDiagonalScale U d e)ᵀ=1)
    (hZcol : (positiveDiagonalScale U d e)ᵀ*positiveDiagonalScale U d e=1) :
    positiveDiagonalScale U d e=U ∧
      (BipartiteSupportConnected U → ∃ c : ℝ,0<c ∧ (∀ i,d i=c) ∧ ∀ j,e j=c⁻¹) :=
  ⟨positive_diagonal_orthogonal_rigidity U d e hd he hUrow hUcol hZrow hZcol,
    connected_positive_diagonal_scales U d e hd he hUrow hUcol hZrow hZcol⟩
end EntropyDesigns
