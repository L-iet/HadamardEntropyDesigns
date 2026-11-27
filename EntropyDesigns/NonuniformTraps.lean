/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.TrapRationalData
public import EntropyDesigns.TrapFourInterpolation
public import EntropyDesigns.TrapFourFeasibility
public import EntropyDesigns.TrapFourDual
public import EntropyDesigns.TrapFiveInterpolation
public import EntropyDesigns.TrapFiveFeasibility
public import EntropyDesigns.TrapFiveDual
public import EntropyDesigns.CollisionLocalMaxima
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
public import Mathlib.LinearAlgebra.Matrix.Notation
public import EntropyDesigns.HadamardLaws
public import EntropyDesigns.WalshBlocks
@[expose] public section
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section

theorem strict_moment_tangent_collision_local {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hp : feasibleLaw A b p)
    (hStrictTangent : ∀ z∈momentTangentCone A p,z≠0 → lawOverlap p z<0) :
    IsLocalMaxOn collision {q | feasibleLaw A b q} p ∧
      ∃ ε : ℝ,0<ε ∧ ∀ q,feasibleLaw A b q → q≠p → ‖q-p‖<ε → collision q<collision p := by
  classical
  obtain ⟨a,ha,hMargin⟩ := closed_cone_strict_linear_margin (momentTangentCone A p)
    (momentTangentCone_closed A p) (fun z hz t ht => momentTangentCone_smul A p z hz t ht)
    (probabilityOverlapLinear p) (by
      intro z hz hz0
      rw [probabilityOverlapLinear_apply]
      exact hStrictTangent z hz hz0)
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




def dualMomentValues {ι α : Type*} [Fintype ι] (A : Matrix ι α ℝ) (y : ι → ℝ) : α → ℝ :=
  fun x => ∑ i,y i*A i x

theorem dualMomentValues_pairing {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (y : ι → ℝ) (z : α → ℝ) :
    (∑ x,dualMomentValues A y x*z x)=∑ i,y i*(A.mulVec z) i := by
  simp only [dualMomentValues,Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro x hx
  ring

theorem interpolated_supported_kernel_zero {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (p : α → ℝ) (L : α → ι → ℝ)
    (hInterpolation : ∀ x,p x≠0 → ∀ t,p t≠0 → (∑ i,L x i*A i t)=if t=x then 1 else 0)
    (z : α → ℝ) (hAz : A.mulVec z=0) (hSupport : ∀ x,p x=0 → z x=0) : z=0 := by
  classical
  funext x
  by_cases hx : p x=0
  · exact hSupport x hx
  · have hPair (t : α) : dualMomentValues A (L x) t*z t=if t=x then z x else 0 := by
      by_cases ht : p t=0
      · have htx : t≠x := fun h => hx (h ▸ ht)
        simp [hSupport t ht,htx]
      · unfold dualMomentValues
        rw [hInterpolation x hx t ht]
        by_cases htx : t=x <;> simp [htx]
    have hh := dualMomentValues_pairing A (L x) z
    rw [hAz] at hh
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hh
    simp_rw [hPair] at hh
    simpa using hh

theorem dual_interpolation_strict_tangent {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (p : α → ℝ) (y : ι → ℝ) (L : α → ι → ℝ)
    (hEqual : ∀ x,p x≠0 → dualMomentValues A y x=p x)
    (hOutside : ∀ x,p x=0 → 0<dualMomentValues A y x)
    (hInterpolation : ∀ x,p x≠0 → ∀ t,p t≠0 → (∑ i,L x i*A i t)=if t=x then 1 else 0) :
    ∀ z∈momentTangentCone A p,z≠0 → lawOverlap p z<0 := by
  classical
  intro z hz hz0
  have hTerm (x : α) : 0≤(dualMomentValues A y x-p x)*z x := by
    by_cases hx : p x=0
    · rw [hx,sub_zero];exact mul_nonneg (hOutside x hx).le (hz.2.2 x hx)
    · rw [hEqual x hx,sub_self,zero_mul]
  have hSumNonneg : 0≤∑ x,(dualMomentValues A y x-p x)*z x := Finset.sum_nonneg (fun x _ => hTerm x)
  have hId := dualMomentValues_pairing A y z
  rw [hz.1] at hId
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hId
  have hGap : (∑ x,(dualMomentValues A y x-p x)*z x)= -lawOverlap p z := by
    simp only [sub_mul,Finset.sum_sub_distrib,hId,zero_sub,lawOverlap]
  by_contra hNot
  have hNonneg : 0≤lawOverlap p z := le_of_not_gt hNot
  have hSumZero : (∑ x,(dualMomentValues A y x-p x)*z x)=0 := by linarith
  have hSupport (x : α) (hx : p x=0) : z x=0 := by
    have hSingle := Finset.single_le_sum (fun t (_ : t∈Finset.univ) => hTerm t) (Finset.mem_univ x)
    rw [hSumZero,hx,sub_zero] at hSingle
    have hMul : dualMomentValues A y x*z x=0 := le_antisymm hSingle (by simpa only [hx,sub_zero] using hTerm x)
    exact (mul_eq_zero.mp hMul).resolve_left (hOutside x hx).ne'
  exact hz0 (interpolated_supported_kernel_zero A p L hInterpolation z hz.1 hSupport)

theorem dual_interpolation_local_collision {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ) (hp : feasibleLaw A b p)
    (y : ι → ℝ) (L : α → ι → ℝ)
    (hEqual : ∀ x,p x≠0 → dualMomentValues A y x=p x)
    (hOutside : ∀ x,p x=0 → 0<dualMomentValues A y x)
    (hInterpolation : ∀ x,p x≠0 → ∀ t,p t≠0 → (∑ i,L x i*A i t)=if t=x then 1 else 0) :
    IsLocalMaxOn collision {q | feasibleLaw A b q} p ∧
      ∃ ε : ℝ,0<ε ∧ ∀ q,feasibleLaw A b q → q≠p → ‖q-p‖<ε → collision q<collision p :=
  strict_moment_tangent_collision_local A b p hp (dual_interpolation_strict_tangent A p y L hEqual hOutside hInterpolation)


theorem rationalTrapMomentMatrix_real (d : ℕ) (r : SmallTrapMomentIndex d) (x : Fin d → Bool) :
    (rationalTrapMomentMatrix d r x : ℝ)=cubeProbabilityMomentMatrix d r x := by
  rcases r with u|i|⟨i,j⟩ <;> simp [rationalTrapMomentMatrix,cubeProbabilityMomentMatrix]

theorem rationalTrapMomentTarget_real (d : ℕ) (r : SmallTrapMomentIndex d) :
    (rationalTrapMomentTarget d r : ℝ)=cubeProbabilityMomentTarget d r := by
  rcases r with u|i|⟨i,j⟩ <;> simp [rationalTrapMomentTarget,cubeProbabilityMomentTarget]
  all_goals split_ifs <;> norm_num

theorem rational_trap_feasible_to_cube {d : ℕ} (p : (Fin d → Bool) → ℚ)
    (hPos : ∀ x,0≤p x) (hMass : ∑ x,p x=1)
    (hMoments : ∀ r,(∑ x,p x*rationalTrapMomentMatrix d r x)=rationalTrapMomentTarget d r) :
    cubeProbabilityFeasible (fun x => (p x : ℝ)) := by
  apply (cube_probability_feasible_iff _).mpr
  refine ⟨?_,?_,?_⟩
  · intro x
    change (0 : ℝ)≤(p x : ℝ)
    exact_mod_cast hPos x
  · change (∑ x,(p x : ℝ))=1
    exact_mod_cast hMass
  · funext r
    have hh : (∑ x,(p x : ℝ)*(rationalTrapMomentMatrix d r x : ℝ))=(rationalTrapMomentTarget d r : ℝ) := by
      exact_mod_cast hMoments r
    simpa only [rationalTrapMomentMatrix_real,rationalTrapMomentTarget_real,Matrix.mulVec,dotProduct,mul_comm] using hh

theorem rational_certificate_strict_cube_local {d : ℕ} (p : (Fin d → Bool) → ℚ)
    (hPos : ∀ x,0≤p x) (hMass : ∑ x,p x=1)
    (hMoments : ∀ r,(∑ x,p x*rationalTrapMomentMatrix d r x)=rationalTrapMomentTarget d r)
    (y : SmallTrapMomentIndex d → ℚ) (L : (Fin d → Bool) → SmallTrapMomentIndex d → ℚ)
    (hDual : ∀ x,(p x≠0 → (∑ r,y r*rationalTrapMomentMatrix d r x)=p x) ∧
      (p x=0 → 0<(∑ r,y r*rationalTrapMomentMatrix d r x)))
    (hInterp : ∀ x t,p x≠0 → p t≠0 → (∑ r,L x r*rationalTrapMomentMatrix d r t)=if t=x then 1 else 0) :
    let pR := fun x => (p x : ℝ)
    cubeProbabilityFeasible pR ∧ IsLocalMaxOn collision {q | cubeProbabilityFeasible q} pR ∧
      ∃ ε : ℝ,0<ε ∧ ∀ q,cubeProbabilityFeasible q → q≠pR → ‖q-pR‖<ε → collision q<collision pR := by
  classical
  let pR := fun x => (p x : ℝ)
  let yR := fun r => (y r : ℝ)
  let LR := fun x r => (L x r : ℝ)
  have hP : cubeProbabilityFeasible pR := rational_trap_feasible_to_cube p hPos hMass hMoments
  have hEqual (x : Fin d → Bool) (hx : pR x≠0) : dualMomentValues (cubeProbabilityMomentMatrix d) yR x=pR x := by
    have hxQ : p x≠0 := by
      have hxR : (p x : ℝ)≠0 := hx
      exact_mod_cast hxR
    have hh : (∑ r,(y r : ℝ)*(rationalTrapMomentMatrix d r x : ℝ))=(p x : ℝ) := by exact_mod_cast (hDual x).1 hxQ
    simpa only [dualMomentValues,yR,pR,rationalTrapMomentMatrix_real] using hh
  have hOutside (x : Fin d → Bool) (hx : pR x=0) : 0<dualMomentValues (cubeProbabilityMomentMatrix d) yR x := by
    have hxQ : p x=0 := by
      have hxR : (p x : ℝ)=0 := hx
      exact_mod_cast hxR
    have hh : (0 : ℝ)<∑ r,(y r : ℝ)*(rationalTrapMomentMatrix d r x : ℝ) := by exact_mod_cast (hDual x).2 hxQ
    simpa only [dualMomentValues,yR,rationalTrapMomentMatrix_real] using hh
  have hInterpolation (x : Fin d → Bool) (hx : pR x≠0) (t : Fin d → Bool) (ht : pR t≠0) :
      (∑ r,LR x r*cubeProbabilityMomentMatrix d r t)=if t=x then 1 else 0 := by
    have hxQ : p x≠0 := by
      have hxR : (p x : ℝ)≠0 := hx
      exact_mod_cast hxR
    have htQ : p t≠0 := by
      have htR : (p t : ℝ)≠0 := ht
      exact_mod_cast htR
    have hh : (∑ r,(L x r : ℝ)*(rationalTrapMomentMatrix d r t : ℝ))=(if t=x then (1 : ℝ) else 0) := by
      have hQ := hInterp x t hxQ htQ
      by_cases htx : t=x
      · rw [if_pos htx] at hQ ⊢
        exact_mod_cast hQ
      · rw [if_neg htx] at hQ ⊢
        exact_mod_cast hQ
    simpa only [LR,rationalTrapMomentMatrix_real] using hh
  obtain ⟨hLocal,hStrict⟩ := dual_interpolation_local_collision (cubeProbabilityMomentMatrix d) (cubeProbabilityMomentTarget d)
    pR ((cube_probability_feasible_iff pR).mp hP) yR LR hEqual hOutside hInterpolation
  have hSet : {q : (Fin d → Bool) → ℝ | cubeProbabilityFeasible q}=
      {q | feasibleLaw (cubeProbabilityMomentMatrix d) (cubeProbabilityMomentTarget d) q} := by ext q;exact cube_probability_feasible_iff q
  refine ⟨hP,?_,?_⟩
  · rw [hSet];exact hLocal
  · obtain ⟨ε,hε,hBound⟩ := hStrict
    exact ⟨ε,hε,fun q hq => hBound q ((cube_probability_feasible_iff q).mp hq)⟩



noncomputable def fourBitTrapLaw (x : Fin 4 → Bool) : ℝ := (fourTrapRationalWeights x : ℝ)
noncomputable def fiveBitTrapLaw (x : Fin 5 → Bool) : ℝ := (fiveTrapRationalWeights x : ℝ)

theorem small_cube_eighth_attainment {d : ℕ} (hd : 2≤d) (hRound : roundedDimension (d+1)=8) :
    ∃ q : (Fin d → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ) := by
  let e : Finset (Fin 3) ≃ Fin 8 := (Fintype.equivFin _).trans (finCongr (by decide))
  have hHad := (walshSquare_hadamard 3).reindex e e
  have hH' : ∃ H : Matrix (Fin (roundedDimension (d+1))) (Fin (roundedDimension (d+1))) ℝ,Matrix.IsHadamard H := by
    rw [hRound]
    exact ⟨_,hHad⟩
  obtain ⟨H,hH⟩ := hH'
  obtain ⟨q,hq,hMass,hMean,hPair,hC,_,_⟩ := cube_law_of_hadamard hd H hH
  refine ⟨q,⟨hq,hMass,hMean,hPair⟩,?_⟩
  simpa only [hRound,Nat.cast_ofNat] using hC

theorem four_bit_nonglobal_trap :
    (∀ x : Fin 4 → Bool,fourBitTrapLaw x=if fourTrapNegativeCount x=0 then (1/6 : ℝ) else if fourTrapNegativeCount x=2 ∨ fourTrapNegativeCount x=3 then 1/12 else 0) ∧
    cubeProbabilityFeasible fourBitTrapLaw ∧ collision fourBitTrapLaw=(7/72 : ℝ) ∧
    IsLocalMaxOn collision {q | cubeProbabilityFeasible q} fourBitTrapLaw ∧
    (∃ ε : ℝ,0<ε ∧ ∀ q : (Fin 4 → Bool) → ℝ,cubeProbabilityFeasible q → q≠fourBitTrapLaw →
      ‖q-fourBitTrapLaw‖<ε → collision q<collision fourBitTrapLaw) ∧
    (∃ q : (Fin 4 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ) ∧ collision fourBitTrapLaw<collision q) := by
  have hData := fourTrap_rational_feasibility
  obtain ⟨hP,hLocal,hStrict⟩ := rational_certificate_strict_cube_local fourTrapRationalWeights
    hData.1 hData.2.1 hData.2.2.1 fourTrapRationalDual fourTrapRationalInterpolation
    fourTrap_rational_dual fourTrap_rational_interpolation
  have hCollision : collision fourBitTrapLaw=(7/72 : ℝ) := by
    unfold collision fourBitTrapLaw
    have hh := congrArg (fun r : ℚ => (r : ℝ)) hData.2.2.2
    push_cast at hh
    norm_num at hh
    exact hh
  have hFormula : ∀ x : Fin 4 → Bool,fourBitTrapLaw x=if fourTrapNegativeCount x=0 then (1/6 : ℝ) else if fourTrapNegativeCount x=2 ∨ fourTrapNegativeCount x=3 then 1/12 else 0 := by
    intro x
    unfold fourBitTrapLaw fourTrapRationalWeights
    split_ifs <;> norm_num
  obtain ⟨q,hq,hC⟩ := small_cube_eighth_attainment (d := 4) (by decide) (by decide)
  refine ⟨hFormula,hP,hCollision,hLocal,hStrict,q,hq,hC,?_⟩
  rw [hCollision,hC]
  norm_num


theorem five_bit_nonglobal_trap :
    (∀ x : Fin 5 → Bool,fiveBitTrapLaw x=if fiveTrapNegativeCount x=0 then (1/6 : ℝ) else if fiveTrapNegativeCount x=3 then 1/12 else 0) ∧
    cubeProbabilityFeasible fiveBitTrapLaw ∧ collision fiveBitTrapLaw=(7/72 : ℝ) ∧
    IsLocalMaxOn collision {q | cubeProbabilityFeasible q} fiveBitTrapLaw ∧
    (∃ ε : ℝ,0<ε ∧ ∀ q : (Fin 5 → Bool) → ℝ,cubeProbabilityFeasible q → q≠fiveBitTrapLaw →
      ‖q-fiveBitTrapLaw‖<ε → collision q<collision fiveBitTrapLaw) ∧
    (∃ q : (Fin 5 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ) ∧ collision fiveBitTrapLaw<collision q) := by
  have hData := fiveTrap_rational_feasibility
  obtain ⟨hP,hLocal,hStrict⟩ := rational_certificate_strict_cube_local fiveTrapRationalWeights
    hData.1 hData.2.1 hData.2.2.1 fiveTrapRationalDual fiveTrapRationalInterpolation
    fiveTrap_rational_dual fiveTrap_rational_interpolation
  have hCollision : collision fiveBitTrapLaw=(7/72 : ℝ) := by
    unfold collision fiveBitTrapLaw
    have hh := congrArg (fun r : ℚ => (r : ℝ)) hData.2.2.2
    push_cast at hh
    norm_num at hh
    exact hh
  have hFormula : ∀ x : Fin 5 → Bool,fiveBitTrapLaw x=if fiveTrapNegativeCount x=0 then (1/6 : ℝ) else if fiveTrapNegativeCount x=3 then 1/12 else 0 := by
    intro x
    unfold fiveBitTrapLaw fiveTrapRationalWeights
    split_ifs <;> norm_num
  obtain ⟨q,hq,hC⟩ := small_cube_eighth_attainment (d := 5) (by decide) (by decide)
  refine ⟨hFormula,hP,hCollision,hLocal,hStrict,q,hq,hC,?_⟩
  rw [hCollision,hC]
  norm_num


end
end EntropyDesigns
