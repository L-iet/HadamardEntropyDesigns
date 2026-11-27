/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace EntropyDesigns.Quantum
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The skew operator on two unit directions is a contraction. -/
theorem unit_rank_one_wedge_norm_le (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖InnerProductSpace.rankOne ℝ u v-InnerProductSpace.rankOne ℝ v u‖≤1 := by
  have huu : Inner.inner ℝ u u=1 := by rw [real_inner_self_eq_norm_sq,hu];norm_num
  have hvv : Inner.inner ℝ v v=1 := by rw [real_inner_self_eq_norm_sq,hv];norm_num
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  let c := Inner.inner ℝ u v
  let a := Inner.inner ℝ v x
  let b := Inner.inner ℝ u x
  let w := v-c • u
  let z := x-b • u
  have hwz : Inner.inner ℝ w z=a-c*b := by
    simp only [w,z,a,b,c,inner_sub_left,inner_sub_right,real_inner_smul_left,
      real_inner_smul_right,huu,real_inner_comm v u] <;> ring
  have hww : Inner.inner ℝ w w=1-c^2 := by
    simp only [w,c,inner_sub_left,inner_sub_right,real_inner_smul_left,
      real_inner_smul_right,huu,hvv,real_inner_comm v u] <;> ring
  have hzz : Inner.inner ℝ z z=‖x‖^2-b^2 := by
    simp only [z,b,inner_sub_left,inner_sub_right,real_inner_smul_left,
      real_inner_smul_right,huu,real_inner_comm x u,real_inner_self_eq_norm_sq x] <;> ring
  have hcs := real_inner_mul_inner_self_le w z
  rw [hwz,hww,hzz] at hcs
  have hvalue : ‖(InnerProductSpace.rankOne ℝ u v-InnerProductSpace.rankOne ℝ v u) x‖^2=
      a^2+b^2-2*c*a*b := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [ContinuousLinearMap.sub_apply,InnerProductSpace.rankOne_apply,a,b,c,
      inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
      huu,hvv,real_inner_comm v u] <;> ring
  have hs : ‖(InnerProductSpace.rankOne ℝ u v-InnerProductSpace.rankOne ℝ v u) x‖^2≤‖x‖^2 := by
    rw [hvalue]
    nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg ‖x‖)]
  simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg x)).mp hs

def rankOneEffect (lam : ℝ) (u : E) : E →L[ℝ] E := lam • InnerProductSpace.rankOne ℝ u u

theorem unit_effect_defect_norm (lam : ℝ) (hlam : 0≤lam) (hlam1 : lam≤1)
    (u : E) (hu : ‖u‖=1) :
    ‖rankOneEffect lam u-rankOneEffect lam u*rankOneEffect lam u‖=lam*(1-lam) := by
  have hp : InnerProductSpace.rankOne ℝ u u*InnerProductSpace.rankOne ℝ u u=
      InnerProductSpace.rankOne ℝ u u := InnerProductSpace.isIdempotentElem_rankOne_self hu
  have he : rankOneEffect lam u-rankOneEffect lam u*rankOneEffect lam u=
      (lam-lam*lam) • InnerProductSpace.rankOne ℝ u u := by
    unfold rankOneEffect
    rw [smul_mul_smul_comm,hp,← sub_smul]
  have hn : 0≤lam-lam*lam := by nlinarith
  rw [he,norm_smul,InnerProductSpace.norm_rankOne,hu]
  simp only [Real.norm_eq_abs,abs_of_nonneg hn,mul_one]
  ring

theorem unit_effect_commutator_bound (lam : ℝ) (u v : E) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖rankOneEffect lam u*rankOneEffect lam v-rankOneEffect lam v*rankOneEffect lam u‖≤
      lam^2*|Inner.inner ℝ u v| := by
  have he : rankOneEffect lam u*rankOneEffect lam v-rankOneEffect lam v*rankOneEffect lam u=
      (lam^2*Inner.inner ℝ u v) •
        (InnerProductSpace.rankOne ℝ u v-InnerProductSpace.rankOne ℝ v u) := by
    unfold rankOneEffect
    simp only [smul_mul_smul_comm,ContinuousLinearMap.mul_def,InnerProductSpace.rankOne_comp_rankOne,
      smul_smul,real_inner_comm v u]
    simp only [smul_sub,pow_two,mul_assoc]
  rw [he,norm_smul]
  have hs := mul_le_mul_of_nonneg_left (unit_rank_one_wedge_norm_le u v hu hv)
    (norm_nonneg (lam^2*Inner.inner ℝ u v))
  simpa [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg lam)] using hs
end
end EntropyDesigns.Quantum
