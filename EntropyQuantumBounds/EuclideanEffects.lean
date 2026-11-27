/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyQuantum.RankOneAlgebra
public import EntropyQuantumBounds.UnitRankOneNorm
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic.FieldSimp
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def rowEuclidean (v : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 v
def normalizedRow (N : ℝ) (v : ι → ℝ) : EuclideanSpace ℝ ι :=
  (Real.sqrt N)⁻¹ • rowEuclidean v
def euclideanOperatorNorm (A : Matrix ι ι ℝ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜:=ℝ) A‖

theorem rowEuclidean_inner (v w : ι → ℝ) :
    Inner.inner ℝ (rowEuclidean v) (rowEuclidean w)=inner v w := by
  simp [rowEuclidean,PiLp.inner_apply,inner,RCLike.inner_apply,mul_comm]

theorem rowEuclidean_norm_sq (v : ι → ℝ) : ‖rowEuclidean v‖^2=inner v v := by
  rw [← real_inner_self_eq_norm_sq,rowEuclidean_inner]

theorem normalizedRow_norm (N : ℝ) (hN : 0<N) (v : ι → ℝ) (hnorm : inner v v=N) :
    ‖normalizedRow N v‖=1 := by
  have hs : Real.sqrt N≠0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have hh : Inner.inner ℝ (normalizedRow N v) (normalizedRow N v)=1 := by
    simp only [normalizedRow,real_inner_smul_left,real_inner_smul_right,rowEuclidean_inner,hnorm]
    field_simp [hs] <;> nlinarith [Real.sq_sqrt hN.le]
  rw [real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (normalizedRow N v)]

theorem normalizedRow_inner (N : ℝ) (hN : 0<N) (v w : ι → ℝ) :
    Inner.inner ℝ (normalizedRow N v) (normalizedRow N w)=inner v w/N := by
  have hs : Real.sqrt N≠0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  simp only [normalizedRow,real_inner_smul_left,real_inner_smul_right,rowEuclidean_inner]
  have hsq := Real.sq_sqrt hN.le
  field_simp [hs,ne_of_gt hN]
  simp only [hsq] <;> ring

theorem effect_toEuclideanCLM (a : ℝ) (v : ι → ℝ) :
    Matrix.toEuclideanCLM (𝕜:=ℝ) (effect a v)=
      a • InnerProductSpace.rankOne ℝ (rowEuclidean v) (rowEuclidean v) := by
  apply ContinuousLinearMap.ext
  intro x
  have hip : Inner.inner ℝ (rowEuclidean v) x=∑ j,v j*x.ofLp j := by
    simp [rowEuclidean,PiLp.inner_apply,RCLike.inner_apply,mul_comm]
  apply PiLp.ext
  intro i
  change (∑ j,(a*(v i*v j))*x.ofLp j)=a*((Inner.inner ℝ (rowEuclidean v) x)*v i)
  rw [hip]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem effect_normalized_rankOne (a N : ℝ) (hN : 0<N) (v : ι → ℝ) :
    Matrix.toEuclideanCLM (𝕜:=ℝ) (effect a v)=
      rankOneEffect (a*N) (normalizedRow N v) := by
  have hs : Real.sqrt N≠0 := ne_of_gt (Real.sqrt_pos.mpr hN)
  have hrank : InnerProductSpace.rankOne ℝ (normalizedRow N v) (normalizedRow N v)=
      N⁻¹ • InnerProductSpace.rankOne ℝ (rowEuclidean v) (rowEuclidean v) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [normalizedRow,InnerProductSpace.rankOne_apply,real_inner_smul_left,
      ContinuousLinearMap.smul_apply,smul_smul]
    congr 1
    have hsq := Real.sq_sqrt hN.le
    field_simp [hs,ne_of_gt hN]
    simp only [hsq] <;> ring
  rw [effect_toEuclideanCLM]
  unfold rankOneEffect
  rw [hrank,smul_smul]
  congr 1
  field_simp [ne_of_gt hN]
end
end EntropyDesigns.Quantum
