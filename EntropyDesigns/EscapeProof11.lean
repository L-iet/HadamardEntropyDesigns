/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.EscapeProof10
public import EntropyDesigns.FourBitSharpBarrier
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
set_option Elab.async false
@[expose] public section
set_option maxHeartbeats 4000000
namespace EntropyDesigns
open Set
theorem exposed_segment_supported_kernel {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p q : α → ℝ)
    (hp : feasibleLaw A b p) (hq : feasibleLaw A b q)
    (hEdge : IsExposed ℝ {v | feasibleLaw A b v} (segment ℝ p q))
    (c : ℝ) (hc : 0<c)
    (hLower : ∀ x, (p x+q x)/2=0 ∨ c ≤ (p x+q x)/2)
    (z : α → ℝ) (hAz : A.mulVec z=0) (hSum : ∑ x, z x=0)
    (hSupport : ∀ x, p x=0 → q x=0 → z x=0) :
    ∃ r : ℝ, z=r • (q-p) := by
  classical
  let m : α → ℝ := fun x => (p x+q x)/2
  have hm : feasibleLaw A b m := by
    refine ⟨fun x => div_nonneg (add_nonneg (hp.1 x) (hq.1 x)) (by norm_num),?_,?_⟩
    · change (∑ x, (p x+q x)/2)=1
      rw [← Finset.sum_div,Finset.sum_add_distrib,hp.2.1,hq.2.1]
      norm_num
    · have hFn : m=(1/2:ℝ) • p+(1/2:ℝ) • q := by ext x; simp [m]; ring
      rw [hFn,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,hp.2.2,hq.2.2]
      ext j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
  let t : ℝ := c/(2*(1+‖z‖))
  have hDen : 0<2*(1+‖z‖) := by positivity
  have ht : 0<t := div_pos hc hDen
  have htEq : t*(2*(1+‖z‖))=c := div_mul_cancel₀ c (ne_of_gt hDen)
  have htN : t*‖z‖ ≤ c := by nlinarith [norm_nonneg z]
  have hCoord (x : α) : |z x| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm z x
  have hNonneg (s : ℝ) (hs : s=t ∨ s= -t) (x : α) : 0 ≤ m x+s*z x := by
    rcases hLower x with h0|hL
    · have hP0 : p x=0 := by have hP:=hp.1 x; have hQ:=hq.1 x; linarith
      have hQ0 : q x=0 := by have hP:=hp.1 x; have hQ:=hq.1 x; linarith
      have hZ := hSupport x hP0 hQ0
      simp [m,hP0,hQ0,hZ]
    · have hZi := abs_le.mp (hCoord x)
      have hLo := mul_le_mul_of_nonneg_left hZi.1 ht.le
      have hHi := mul_le_mul_of_nonneg_left hZi.2 ht.le
      change c ≤ m x at hL
      rcases hs with rfl|rfl <;> nlinarith
  have hFeasible (s : ℝ) (hs : s=t ∨ s= -t) :
      feasibleLaw A b (fun x => m x+s*z x) := by
    refine ⟨hNonneg s hs,?_,?_⟩
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum,hSum,mul_zero,add_zero,hm.2.1]
    · change A.mulVec (m+s • z)=b
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,hm.2.2,hAz,smul_zero,add_zero]
  let v : α → ℝ := fun x => m x+t*z x
  let w : α → ℝ := fun x => m x-t*z x
  have hv : feasibleLaw A b v := hFeasible t (Or.inl rfl)
  have hw : feasibleLaw A b w := by
    simpa only [w,neg_mul,sub_eq_add_neg] using hFeasible (-t) (Or.inr rfl)
  have hMedge : m∈segment ℝ p q := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,m]
    ring
  have hMopen : m∈openSegment ℝ v w := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext x
    change (1/2:ℝ)*(m x+t*z x)+(1/2:ℝ)*(m x-t*z x)=m x
    ring
  have hVedge := hEdge.isExtreme.left_mem_of_mem_openSegment hv hw hMedge hMopen
  rw [segment_eq_image] at hVedge
  obtain ⟨u,hu,hEq⟩ := hVedge
  refine ⟨(u-1/2)/t,?_⟩
  funext x
  have hh := congrFun hEq x
  change (1-u)*p x+u*q x=(p x+q x)/2+t*z x at hh
  change z x=((u-1/2)/t)*(q x-p x)
  apply (mul_left_cancel₀ ht.ne')
  calc
    t*z x=(u-1/2)*(q x-p x) := by nlinarith only [hh]
    _=t*(((u-1/2)/t)*(q x-p x)) := by field_simp


end EntropyDesigns
