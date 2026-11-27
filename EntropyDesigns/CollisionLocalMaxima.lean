/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Modified imports for bounded compilation; mathematical statements and proof bodies are unchanged. -/
module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.NoncommRing
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import EntropyDesigns.SupportVertex
public import EntropyDesigns.SignLaws
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns
open Filter Set
open scoped Topology
noncomputable section

theorem squared_norm_increment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w v : E) (t : ℝ) :
    ‖w+t • (v-w)‖^2=‖w‖^2+2*t*Inner.inner ℝ w (v-w)+t^2*‖v-w‖^2 := by
  rw [norm_add_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

theorem local_norm_max_strictly_exposes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : Set E) (hP : Convex ℝ P) (w : E) (hw : w∈P)
    (hMax : IsLocalMaxOn (fun x : E => ‖x‖^2) P w) :
    ∀ v∈P,v≠w → Inner.inner ℝ w (v-w)<0 := by
  intro v hv hvw
  by_contra hNeg
  have hDot : 0 ≤ Inner.inner ℝ w (v-w) := le_of_not_gt hNeg
  let g : ℝ → E := fun t => w+t • (v-w)
  have hCont : Tendsto g (𝓝[>] 0) (𝓝 w) := by
    have hId : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hV : Tendsto (fun _ : ℝ => v-w) (𝓝[>] 0) (𝓝 (v-w)) := tendsto_const_nhds
    have hW : Tendsto (fun _ : ℝ => w) (𝓝[>] 0) (𝓝 w) := tendsto_const_nhds
    have hh := hW.add (hId.smul hV)
    simpa only [zero_smul,add_zero] using hh
  have hWithin : Tendsto g (𝓝[>] 0) (𝓝[P] w) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hCont,?_⟩
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with t ht ht1
    exact hP.add_smul_sub_mem hw hv ⟨le_of_lt ht,le_of_lt ht1⟩
  have hBound : ∀ᶠ t in 𝓝[>] (0 : ℝ),‖g t‖^2≤‖w‖^2 := hWithin hMax
  have hPositive : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),0<t := self_mem_nhdsWithin
  obtain ⟨t,ht,hBt⟩ := (hPositive.and hBound).exists
  have ht' : (0 : ℝ)<t := ht
  have hNorm : 0<‖v-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw)
  have hInc := squared_norm_increment w v t
  change ‖w+t • (v-w)‖^2≤‖w‖^2 at hBt
  nlinarith [mul_nonneg ht'.le hDot,mul_pos (sq_pos_of_pos ht') (sq_pos_of_pos hNorm)]

theorem finite_exposure_margin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset E) (w : E) (hS : ∀ v∈S,v≠w → Inner.inner ℝ w (v-w)<0) :
    ∃ a : ℝ,0<a ∧ ∀ v∈S,Inner.inner ℝ w (v-w)≤ -a*‖v-w‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert v S hv ih =>
    obtain ⟨a,ha,hMargin⟩ := ih (fun u hu => hS u (Finset.mem_insert_of_mem hu))
    by_cases hvw : v=w
    · refine ⟨a,ha,?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with hEq|hu
      · subst u;simp [hvw]
      · exact hMargin u hu
    · have hDot := hS v (Finset.mem_insert_self v S) hvw
      have hNorm : 0<‖v-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw)
      let b := min a (-Inner.inner ℝ w (v-w)/‖v-w‖)
      have hb : 0<b := lt_min ha (div_pos (neg_pos.mpr hDot) hNorm)
      refine ⟨b,hb,?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with hEq|hu
      · subst u
        have hB : b*‖v-w‖≤ -Inner.inner ℝ w (v-w) :=
          (le_div_iff₀ hNorm).mp (min_le_right a _)
        linarith
      · have hB : b≤a := min_le_left _ _
        have hN := norm_nonneg (u-w)
        nlinarith [hMargin u hu]


theorem exposure_margin_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) (a : ℝ) (ha : 0≤a) :
    Convex ℝ {v : E | Inner.inner ℝ w (v-w)≤ -a*‖v-w‖} := by
  intro x hx y hy c d hc hd hcd
  have hVec : c • x+d • y-w=c • (x-w)+d • (y-w) := by
    calc
      _=c • x+d • y-(c+d) • w := by rw [hcd,one_smul]
      _=_ := by module
  change Inner.inner ℝ w (c • x+d • y-w)≤ -a*‖c • x+d • y-w‖
  rw [hVec,inner_add_right,inner_smul_right,inner_smul_right]
  have hNorm := norm_add_le (c • (x-w)) (d • (y-w))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hc,abs_of_nonneg hd] at hNorm
  have h1 := mul_le_mul_of_nonneg_left hx hc
  have h2 := mul_le_mul_of_nonneg_left hy hd
  have h3 := mul_le_mul_of_nonneg_left hNorm ha
  nlinarith

theorem finite_strict_exposure_gives_local_max {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset E) (w : E) (hw : w∈convexHull ℝ (S : Set E))
    (hExpose : ∀ v∈convexHull ℝ (S : Set E),v≠w → Inner.inner ℝ w (v-w)<0) :
    IsLocalMaxOn (fun x : E => ‖x‖^2) (convexHull ℝ (S : Set E)) w ∧
      (∃ ε : ℝ,0<ε ∧ ∀ v∈convexHull ℝ (S : Set E),v≠w → ‖v-w‖<ε → ‖v‖^2<‖w‖^2) ∧
      w∈(convexHull ℝ (S : Set E)).extremePoints ℝ := by
  classical
  let P := convexHull ℝ (S : Set E)
  have hSeed : ∀ v∈S,v≠w → Inner.inner ℝ w (v-w)<0 := fun v hv => hExpose v (subset_convexHull ℝ (S : Set E) hv)
  obtain ⟨a,ha,hMargin⟩ := finite_exposure_margin S w hSeed
  have hHull : ∀ v∈P,Inner.inner ℝ w (v-w)≤ -a*‖v-w‖ := by
    exact convexHull_min hMargin (exposure_margin_convex w a ha.le)
  have hStrict (v : E) (hv : v∈P) (hvw : v≠w) (hClose : ‖v-w‖<2*a) : ‖v‖^2<‖w‖^2 := by
    have hM := hHull v hv
    have hN : 0<‖v-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hvw)
    have hInc := squared_norm_increment w v 1
    simp only [one_smul,add_sub_cancel,one_mul,one_pow] at hInc
    nlinarith [mul_pos hN (sub_pos.mpr hClose)]
  have hLocal : IsLocalMaxOn (fun x : E => ‖x‖^2) P w := by
    have hBall : ∀ᶠ v : E in 𝓝 w,‖v-w‖<2*a := by
      simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds w (by linarith : 0<2*a)
    have hMem : ∀ᶠ v : E in 𝓝[P] w,v∈P := self_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds hBall,hMem] with v hClose hv
    by_cases hvw : v=w
    · subst v;exact le_rfl
    · exact (hStrict v hv hvw hClose).le
  have hExtreme : w∈P.extremePoints ℝ := by
    apply exposedPoints_subset_extremePoints
    refine ⟨hw,innerSL ℝ w,?_⟩
    intro v hv
    by_cases hvw : v=w
    · subst v;exact ⟨le_rfl,fun _ => rfl⟩
    · have hE := hExpose v hv hvw
      rw [inner_sub_right] at hE
      constructor
      · exact (sub_neg.mp hE).le
      · intro hContra
        change Inner.inner ℝ w w ≤ Inner.inner ℝ w v at hContra
        exfalso;linarith
  exact ⟨hLocal,⟨2*a,by linarith,hStrict⟩,hExtreme⟩



theorem finite_polytope_local_max_criterion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset E) (w : E) (hw : w∈convexHull ℝ (S : Set E)) :
    (IsLocalMaxOn (fun x : E => ‖x‖^2) (convexHull ℝ (S : Set E)) w ↔
      ∀ v∈convexHull ℝ (S : Set E),Inner.inner ℝ w v≤ Inner.inner ℝ w w ∧
        (Inner.inner ℝ w w ≤ Inner.inner ℝ w v → v=w)) ∧
    (IsLocalMaxOn (fun x : E => ‖x‖^2) (convexHull ℝ (S : Set E)) w →
      (∃ ε : ℝ,0<ε ∧ ∀ v∈convexHull ℝ (S : Set E),v≠w → ‖v-w‖<ε → ‖v‖^2<‖w‖^2) ∧
      w∈(convexHull ℝ (S : Set E)).extremePoints ℝ) := by
  have hForward (hLocal : IsLocalMaxOn (fun x : E => ‖x‖^2) (convexHull ℝ (S : Set E)) w) :
      ∀ v∈convexHull ℝ (S : Set E),v≠w → Inner.inner ℝ w (v-w)<0 :=
    local_norm_max_strictly_exposes _ (convex_convexHull ℝ (S : Set E)) w hw hLocal
  have hReverse (hLinear : ∀ v∈convexHull ℝ (S : Set E),Inner.inner ℝ w v≤ Inner.inner ℝ w w ∧
      (Inner.inner ℝ w w ≤ Inner.inner ℝ w v → v=w)) :
      ∀ v∈convexHull ℝ (S : Set E),v≠w → Inner.inner ℝ w (v-w)<0 := by
    intro v hv hvw
    obtain ⟨hLe,hUnique⟩ := hLinear v hv
    have hNe : Inner.inner ℝ w v≠ Inner.inner ℝ w w := fun h => hvw (hUnique h.symm.le)
    rw [inner_sub_right]
    exact sub_neg.mpr (lt_of_le_of_ne hLe hNe)
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro hLocal v hv
    by_cases hvw : v=w
    · subst v;exact ⟨le_rfl,fun _ => rfl⟩
    · have hE := hForward hLocal v hv hvw
      rw [inner_sub_right] at hE
      exact ⟨(sub_neg.mp hE).le,fun h => False.elim (not_le_of_gt (sub_neg.mp hE) h)⟩
  · intro hLinear
    exact (finite_strict_exposure_gives_local_max S w hw (hReverse hLinear)).1
  · intro hLocal
    exact (finite_strict_exposure_gives_local_max S w hw (hForward hLocal)).2



theorem uniform_vertex_supported_kernel_zero {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hp : feasibleLaw A b p)
    (hVertex : p∈Set.extremePoints ℝ {q | feasibleLaw A b q})
    (c : ℝ) (hc : 0<c) (hUniform : ∀ i,p i=0 ∨ p i=c)
    (z : α → ℝ) (hAz : A.mulVec z=0) (hSum : ∑ i,z i=0)
    (hSupport : ∀ i,p i=0 → z i=0) : z=0 := by
  classical
  let t := c/(2*(1+‖z‖))
  have hD : 0<2*(1+‖z‖) := by positivity
  have ht : 0<t := div_pos hc hD
  have htEq : t*(2*(1+‖z‖))=c := div_mul_cancel₀ c (ne_of_gt hD)
  have htN : t*‖z‖≤c := by nlinarith [norm_nonneg z]
  have hCoords (i : α) : |z i|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  have hNonneg (s : ℝ) (hs : s=t ∨ s= -t) (i : α) : 0≤p i+s*z i := by
    rcases hUniform i with hp0|hpc
    · rw [hp0,hSupport i hp0];simp
    · have hzi := abs_le.mp (hCoords i)
      have hLo := mul_le_mul_of_nonneg_left hzi.1 ht.le
      have hHi := mul_le_mul_of_nonneg_left hzi.2 ht.le
      rcases hs with rfl|rfl <;> rw [hpc] <;> nlinarith
  have hFeasible (s : ℝ) (hs : s=t ∨ s= -t) : feasibleLaw A b (fun i => p i+s*z i) := by
    refine ⟨hNonneg s hs,?_,?_⟩
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum,hSum,mul_zero,add_zero,hp.2.1]
    · change A.mulVec (p+s • z)=b
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,hp.2.2,hAz,smul_zero,add_zero]
  let q : α → ℝ := fun i => p i+t*z i
  let r : α → ℝ := fun i => p i-t*z i
  have hq : feasibleLaw A b q := hFeasible t (Or.inl rfl)
  have hr : feasibleLaw A b r := by simpa only [r,neg_mul,sub_eq_add_neg] using hFeasible (-t) (Or.inr rfl)
  have hMid : p∈openSegment ℝ q r := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    funext i
    change (1/2 : ℝ)*(p i+t*z i)+(1/2 : ℝ)*(p i-t*z i)=p i
    ring
  have hqp : q=p := hVertex.2 hq hr hMid
  funext i
  have hh := congrFun hqp i
  change p i+t*z i=p i at hh
  have hm : t*z i=0 := by linarith
  exact (mul_eq_zero.mp hm).resolve_left ht.ne'


theorem closed_cone_strict_linear_margin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (C : Set E) (hClosed : IsClosed C)
    (hCone : ∀ z∈C,∀ t : ℝ,0≤t → t • z∈C)
    (L : E →L[ℝ] ℝ) (hStrict : ∀ z∈C,z≠0 → L z<0) :
    ∃ a : ℝ,0<a ∧ ∀ z∈C,L z≤ -a*‖z‖ := by
  classical
  let S := Metric.sphere (0 : E) 1∩C
  have hCompact : IsCompact S := (isCompact_sphere (0 : E) 1).inter_right hClosed
  have hNormalize (z : E) (hz : z∈C) (hz0 : z≠0) : ‖z‖⁻¹ • z∈S := by
    refine ⟨?_,hCone z hz ‖z‖⁻¹ (inv_nonneg.mpr (norm_nonneg z))⟩
    simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
  by_cases hNonempty : S.Nonempty
  · obtain ⟨u,hu,hMax⟩ := hCompact.exists_isMaxOn hNonempty L.continuous.continuousOn
    have hu0 : u≠0 := by
      intro h
      have hh := hu.1
      simp [h] at hh
    have hLu : L u<0 := hStrict u hu.2 hu0
    refine ⟨-L u,neg_pos.mpr hLu,?_⟩
    intro z hz
    by_cases hz0 : z=0
    · simp [hz0]
    · have hN : 0<‖z‖ := norm_pos_iff.mpr hz0
      have hh := hMax (hNormalize z hz hz0)
      change L (‖z‖⁻¹ • z)≤L u at hh
      rw [map_smul,smul_eq_mul] at hh
      have hm := mul_le_mul_of_nonneg_left hh hN.le
      have hCancel : ‖z‖*(‖z‖⁻¹*L z)=L z := by rw [← mul_assoc,mul_inv_cancel₀ hN.ne',one_mul]
      rw [hCancel] at hm
      simpa only [neg_neg,mul_comm] using hm
  · refine ⟨1,by norm_num,?_⟩
    intro z hz
    by_cases hz0 : z=0
    · simp [hz0]
    · exact False.elim (hNonempty ⟨_,hNormalize z hz hz0⟩)


def momentTangentCone {ι α : Type*} [Fintype α] (A : Matrix ι α ℝ) (p : α → ℝ) : Set (α → ℝ) :=
  {z | A.mulVec z=0 ∧ (∑ i,z i)=0 ∧ ∀ i,p i=0 → 0≤z i}

def probabilityOverlapLinear {α : Type*} [Fintype α] (p : α → ℝ) : (α → ℝ) →L[ℝ] ℝ :=
  ∑ i,(p i) • ContinuousLinearMap.proj i

theorem probabilityOverlapLinear_apply {α : Type*} [Fintype α] (p z : α → ℝ) :
    probabilityOverlapLinear p z=lawOverlap p z := by
  simp [probabilityOverlapLinear,lawOverlap]

theorem momentTangentCone_closed {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (p : α → ℝ) : IsClosed (momentTangentCone A p) := by
  have hA : IsClosed {z : α → ℝ | A.mulVec z=0} := isClosed_eq
    (continuous_pi fun i => by simp only [Matrix.mulVec,dotProduct];fun_prop) continuous_const
  have hSum : IsClosed {z : α → ℝ | (∑ i,z i)=0} := isClosed_eq (by fun_prop) continuous_const
  have hOut : IsClosed {z : α → ℝ | ∀ i,p i=0 → 0≤z i} := by
    have hC (i : α) (_ : p i=0) : IsClosed {z : α → ℝ | 0≤z i} :=
      isClosed_le continuous_const (continuous_apply i)
    simpa only [setOf_forall] using isClosed_iInter (fun i => isClosed_iInter (fun h : p i=0 => hC i h))
  exact hA.inter (hSum.inter hOut)

theorem momentTangentCone_smul {ι α : Type*} [Fintype α]
    (A : Matrix ι α ℝ) (p z : α → ℝ) (hz : z∈momentTangentCone A p)
    (t : ℝ) (ht : 0≤t) : t • z∈momentTangentCone A p := by
  refine ⟨?_,?_,?_⟩
  · rw [Matrix.mulVec_smul,hz.1,smul_zero]
  · simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,hz.2.1,mul_zero]
  · intro i hi;exact mul_nonneg ht (hz.2.2 i hi)

theorem uniform_vertex_tangent_strict {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hp : feasibleLaw A b p)
    (hVertex : p∈Set.extremePoints ℝ {q | feasibleLaw A b q})
    (c : ℝ) (hc : 0<c) (hUniform : ∀ i,p i=0 ∨ p i=c)
    (z : α → ℝ) (hz : z∈momentTangentCone A p) (hz0 : z≠0) : lawOverlap p z<0 := by
  classical
  let e := ∑ i,if p i=0 then z i else 0
  have hTerm (i : α) : 0 ≤ (if p i=0 then z i else 0) := by
    by_cases hi : p i=0
    · simp only [hi,ite_true];exact hz.2.2 i hi
    · simp [hi]
  have he : 0≤e := Finset.sum_nonneg (fun i _ => hTerm i)
  have hDot : lawOverlap p z= -c*e := by
    have hPair (i : α) : p i*z i=c*(z i-(if p i=0 then z i else 0)) := by
      by_cases hi : p i=0
      · simp [hi]
      · have hpc := (hUniform i).resolve_left hi
        rw [if_neg hi,sub_zero,hpc]
    unfold lawOverlap
    simp_rw [hPair]
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,hz.2.1]
    dsimp only [e]
    ring
  by_contra hBad
  have he0 : e=0 := by
    have hNot : 0 ≤ lawOverlap p z := le_of_not_gt hBad
    rw [hDot] at hNot
    nlinarith
  have hSupport (i : α) (hi : p i=0) : z i=0 := by
    have hSingle := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hTerm j) (Finset.mem_univ i)
    change (if p i=0 then z i else 0)≤e at hSingle
    rw [hi,if_pos rfl,he0] at hSingle
    linarith [hz.2.2 i hi]
  exact hz0 (uniform_vertex_supported_kernel_zero A b p hp hVertex c hc hUniform z hz.1 hz.2.1 hSupport)



theorem uniform_vertex_strict_local_collision {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hp : feasibleLaw A b p)
    (hVertex : p∈Set.extremePoints ℝ {q | feasibleLaw A b q})
    (c : ℝ) (hc : 0<c) (hUniform : ∀ i,p i=0 ∨ p i=c) :
    IsLocalMaxOn collision {q | feasibleLaw A b q} p ∧
      ∃ ε : ℝ,0<ε ∧ ∀ q,feasibleLaw A b q → q≠p → ‖q-p‖<ε → collision q<collision p := by
  classical
  obtain ⟨a,ha,hMargin⟩ := closed_cone_strict_linear_margin (momentTangentCone A p)
    (momentTangentCone_closed A p) (fun z hz t ht => momentTangentCone_smul A p z hz t ht)
    (probabilityOverlapLinear p) (by
      intro z hz hz0
      rw [probabilityOverlapLinear_apply]
      exact uniform_vertex_tangent_strict A b p hp hVertex c hc hUniform z hz hz0)
  have hDiff (q : α → ℝ) (hq : feasibleLaw A b q) : q-p∈momentTangentCone A p := by
    refine ⟨?_,?_,?_⟩
    · rw [Matrix.mulVec_sub,hq.2.2,hp.2.2,sub_self]
    · simp only [Pi.sub_apply,Finset.sum_sub_distrib,hq.2.1,hp.2.1,sub_self]
    · intro i hi;simpa only [Pi.sub_apply,hi,sub_zero] using hq.1 i
  have hCollisionNorm (z : α → ℝ) : collision z≤(Fintype.card α : ℝ)*‖z‖^2 := by
    unfold collision
    calc
      (∑ i,z i^2)≤∑ _ : α,‖z‖^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hAbs : |z i|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
        have hMul := mul_nonneg (sub_nonneg.mpr hAbs) (add_nonneg (norm_nonneg z) (abs_nonneg (z i)))
        nlinarith [sq_abs (z i)]
      _=_ := by simp
  let ε := a/((Fintype.card α : ℝ)+1)
  have hDen : 0<(Fintype.card α : ℝ)+1 := by positivity
  have hε : 0<ε := div_pos ha hDen
  have hStrict (q : α → ℝ) (hq : feasibleLaw A b q) (hqp : q≠p) (hClose : ‖q-p‖<ε) :
      collision q<collision p := by
    have hM := hMargin (q-p) (hDiff q hq)
    rw [probabilityOverlapLinear_apply] at hM
    have hN : 0<‖q-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
    have hSmall : ‖q-p‖*((Fintype.card α : ℝ)+1)<a := (lt_div_iff₀ hDen).mp hClose
    have hScaled := mul_lt_mul_of_pos_right hSmall hN
    have hInc := collision_direction_expansion p (q-p) 1
    have hFun : (fun i => p i+1*(q-p) i)=q := by funext i;simp
    rw [hFun] at hInc
    simp only [one_mul,one_pow,mul_one] at hInc
    nlinarith [hCollisionNorm (q-p),mul_pos ha hN]
  refine ⟨?_,ε,hε,hStrict⟩
  have hBall : ∀ᶠ q : α → ℝ in 𝓝 p,‖q-p‖<ε := by
    simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds p hε
  have hMem : ∀ᶠ q : α → ℝ in 𝓝[{q | feasibleLaw A b q}] p,feasibleLaw A b q := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds hBall,hMem] with q hClose hq
  by_cases hqp : q=p
  · subst q;exact le_rfl
  · exact (hStrict q hq hqp hClose).le



def cubeProbabilityFeasible {d : ℕ} (w : (Fin d → Bool) → ℝ) : Prop :=
  (∀ x,0≤w x) ∧ (∑ x,w x)=1 ∧
    (∀ i,∑ x,w x*(bitSign (x i) : ℝ)=0) ∧
    (∀ i j,i≠j → ∑ x,w x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)=0)

def cubeProbabilityMomentMatrix (d : ℕ) : Matrix (Unit ⊕ (Fin d ⊕ (Fin d×Fin d))) (Fin d → Bool) ℝ :=
  Sum.elim (fun _ _ => 1)
    (Sum.elim (fun i x => (bitSign (x i) : ℝ))
      (fun ij x => (bitSign (x ij.1) : ℝ)*(bitSign (x ij.2) : ℝ)))

def cubeProbabilityMomentTarget (d : ℕ) : Unit ⊕ (Fin d ⊕ (Fin d×Fin d)) → ℝ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 0) (fun ij => if ij.1=ij.2 then 1 else 0))

theorem cube_probability_feasible_iff {d : ℕ} (w : (Fin d → Bool) → ℝ) :
    cubeProbabilityFeasible w ↔ feasibleLaw (cubeProbabilityMomentMatrix d) (cubeProbabilityMomentTarget d) w := by
  constructor
  · rintro ⟨hPos,hMass,hMean,hPair⟩
    refine ⟨hPos,hMass,?_⟩
    funext c
    rcases c with u|i|⟨i,j⟩
    · simpa [cubeProbabilityMomentMatrix,cubeProbabilityMomentTarget,Matrix.mulVec,dotProduct] using hMass
    · simpa [cubeProbabilityMomentMatrix,cubeProbabilityMomentTarget,Matrix.mulVec,dotProduct,mul_comm] using hMean i
    · by_cases hij : i=j
      · subst j
        have hSq (x : Fin d → Bool) : (bitSign (x i) : ℝ)*(bitSign (x i) : ℝ)=1 := by
          cases x i <;> norm_num [bitSign]
        simp [cubeProbabilityMomentMatrix,cubeProbabilityMomentTarget,Matrix.mulVec,dotProduct,hSq,hMass]
      · simpa [cubeProbabilityMomentMatrix,cubeProbabilityMomentTarget,Matrix.mulVec,dotProduct,hij,mul_assoc,mul_comm,mul_left_comm] using hPair i j hij
  · rintro ⟨hPos,hMass,hMatrix⟩
    refine ⟨hPos,hMass,?_,?_⟩
    · intro i
      have hh := congrFun hMatrix (Sum.inr (Sum.inl i))
      simpa [cubeProbabilityMomentMatrix,cubeProbabilityMomentTarget,Matrix.mulVec,dotProduct,mul_comm] using hh
    · intro i j hij
      have hh := congrFun hMatrix (Sum.inr (Sum.inr (i,j)))
      simpa [cubeProbabilityMomentMatrix,cubeProbabilityMomentTarget,Matrix.mulVec,dotProduct,hij,mul_assoc,mul_comm,mul_left_comm] using hh

theorem uniform_cube_vertex_strict_local_collision {d : ℕ}
    (p : (Fin d → Bool) → ℝ) (hp : cubeProbabilityFeasible p)
    (hVertex : p∈Set.extremePoints ℝ {q | cubeProbabilityFeasible q})
    (c : ℝ) (hc : 0<c) (hUniform : ∀ x,p x=0 ∨ p x=c) :
    IsLocalMaxOn collision {q | cubeProbabilityFeasible q} p ∧
      ∃ ε : ℝ,0<ε ∧ ∀ q,cubeProbabilityFeasible q → q≠p → ‖q-p‖<ε → collision q<collision p := by
  classical
  have hSet : {q : (Fin d → Bool) → ℝ | cubeProbabilityFeasible q}=
      {q | feasibleLaw (cubeProbabilityMomentMatrix d) (cubeProbabilityMomentTarget d) q} := by
    ext q;exact cube_probability_feasible_iff q
  rw [hSet] at hVertex ⊢
  have hh := uniform_vertex_strict_local_collision (cubeProbabilityMomentMatrix d) (cubeProbabilityMomentTarget d)
    p ((cube_probability_feasible_iff p).mp hp) hVertex c hc hUniform
  refine ⟨hh.1,?_⟩
  obtain ⟨ε,hε,hStrict⟩ := hh.2
  exact ⟨ε,hε,fun q hq => hStrict q ((cube_probability_feasible_iff q).mp hq)⟩


end
end EntropyDesigns
