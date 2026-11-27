/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.Collision
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
@[expose] public section
namespace EntropyDesigns.RelativeSequence
noncomputable section
open Filter Set
open scoped Topology BigOperators

theorem collision_increment {A : Type*} [Fintype A]
    (p q : A → ℝ) (t : ℝ) :
    collision (p+t • (q-p)) = collision p +
      2*t*(∑ i,p i*(q i-p i)) + t^2*collision (q-p) := by
  have hpoint (i : A) : (p i+t*(q i-p i))^2 =
      (p i)^2+2*t*(p i*(q i-p i))+t^2*(q i-p i)^2 := by ring
  simp only [collision,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]

theorem collision_positive_of_ne_zero {A : Type*} [Fintype A]
    (v : A → ℝ) (hv : v ≠ 0) : 0 < collision v := by
  classical
  obtain ⟨i,hi⟩ : ∃ i,v i ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext hn)
  exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
    (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

theorem local_collision_strict_exposure {A : Type*} [Fintype A]
    (P : Set (A → ℝ)) (hP : Convex ℝ P) (p : A → ℝ) (hp : p ∈ P)
    (hmax : IsLocalMaxOn collision P p) :
    ∀ q ∈ P,q ≠ p → (∑ i,p i*(q i-p i)) < 0 := by
  intro q hq hqp
  by_contra hn
  have hdot : 0 ≤ ∑ i,p i*(q i-p i) := le_of_not_gt hn
  let g : ℝ → (A → ℝ) := fun t => p+t • (q-p)
  have hc : Tendsto g (𝓝[>] 0) (𝓝 p) := by
    have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hv : Tendsto (fun _ : ℝ => q-p) (𝓝[>] 0) (𝓝 (q-p)) := tendsto_const_nhds
    have hp' : Tendsto (fun _ : ℝ => p) (𝓝[>] 0) (𝓝 p) := tendsto_const_nhds
    simpa only [zero_smul,add_zero] using hp'.add (hi.smul hv)
  have hw : Tendsto g (𝓝[>] 0) (𝓝[P] p) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hc,?_⟩
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with t ht ht1
    exact hP.add_smul_sub_mem hp hq ⟨ht.le,ht1.le⟩
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ),collision (g t) ≤ collision p := hw hmax
  have ht : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ),0<t := self_mem_nhdsWithin
  obtain ⟨t,ht,hb⟩ := (ht.and hb).exists
  have hpos := collision_positive_of_ne_zero (q-p) (sub_ne_zero.mpr hqp)
  have hinc := collision_increment p q t
  change collision (p+t • (q-p)) ≤ collision p at hb
  nlinarith [mul_nonneg ht.le hdot,mul_pos (sq_pos_of_pos ht) hpos]

theorem local_collision_max_extreme {A : Type*} [Fintype A]
    (P : Set (A → ℝ)) (hP : Convex ℝ P) (p : A → ℝ) (hp : p ∈ P)
    (hmax : IsLocalMaxOn collision P p) : p ∈ P.extremePoints ℝ := by
  have hexpose := local_collision_strict_exposure P hP p hp hmax
  refine ⟨hp,?_⟩
  intro x hx y hy hz
  obtain ⟨a,b,ha,hb,hab,hcomb⟩ := hz
  by_contra hxp
  have hxneg := hexpose x hx hxp
  have hyle : (∑ i,p i*(y i-p i)) ≤ 0 := by
    by_cases hyp : y=p
    · subst y
      simp
    · exact (hexpose y hy hyp).le
  have hzero : a*(∑ i,p i*(x i-p i))+b*(∑ i,p i*(y i-p i))=0 := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congrFun hcomb i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hi
    have hm := congrArg (fun z : ℝ => p i*z) hi
    nlinarith
  nlinarith [mul_neg_of_pos_of_neg ha hxneg,mul_nonpos_of_nonneg_of_nonpos hb.le hyle]

end
end EntropyDesigns.RelativeSequence
