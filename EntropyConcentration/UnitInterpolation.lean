/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyConcentration.FaceInterpolation
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns.Concentration.Interpolation
noncomputable section
open scoped BigOperators Topology

def lawOverlap {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * q a

theorem collision_direction_expansion {α : Type*} [Fintype α]
    (p z : α → ℝ) (t : ℝ) :
    collision (fun a => p a + t * z a) =
      collision p + 2 * t * lawOverlap p z + t ^ 2 * collision z := by
  have h : ∀ a, (p a + t * z a) ^ 2 =
      p a ^ 2 + (2 * t) * (p a * z a) + t ^ 2 * z a ^ 2 := by
    intro a
    ring
  unfold collision
  simp_rw [h]
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  unfold lawOverlap
  ring

def outsideLawMass {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (q : α → ℝ) : ℝ :=
  ∑ x∈Sᶜ,q x

theorem unit_interpolation_coordinate_bound {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p q : α → ℝ) (L : S → α → ℝ)
    (hp : ∀ x,x∉S → p x=0) (hq : ∀ x,0≤q x)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (hMoment : ∀ s,∑ x,q x*L s x=∑ x,p x*L s x) :
    ∀ s : S,|q s-p s|≤outsideLawMass S q := by
  classical
  intro s
  have hRestricted (r : α → ℝ) : (∑ x∈S,r x*L s x)=r s := by
    calc
      _=∑ x∈S,if x=s.val then r x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hInterpolation s x hx]
        by_cases hxs : x=s.val <;> simp [hxs]
      _=_ := by simp [s.property]
  have hOutsideP : (∑ x∈Sᶜ,p x*L s x)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hp x (Finset.mem_compl.mp hx),zero_mul]
  have hM := hMoment s
  rw [← Finset.sum_add_sum_compl S (fun x => q x*L s x),
    ← Finset.sum_add_sum_compl S (fun x => p x*L s x),hRestricted q,hRestricted p,hOutsideP,add_zero] at hM
  have hDiff : q s-p s= -(∑ x∈Sᶜ,q x*L s x) := by linarith
  rw [hDiff,abs_neg]
  calc
    _≤∑ x∈Sᶜ,|q x*L s x| := Finset.abs_sum_le_sum_abs _ _
    _≤outsideLawMass S q := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul,abs_of_nonneg (hq x)]
      exact (mul_le_mul_of_nonneg_left (hBound s x) (hq x)).trans_eq (mul_one _)

theorem unit_interpolation_norm_bounds {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p q : α → ℝ) (L : S → α → ℝ)
    (hp : ∀ x,x∉S → p x=0) (hq : ∀ x,0≤q x)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (hMoment : ∀ s,∑ x,q x*L s x=∑ x,p x*L s x) :
    ‖q-p‖≤outsideLawMass S q ∧
      (∑ x,|q x-p x|)≤((S.card : ℝ)+1)*outsideLawMass S q := by
  classical
  have hE : 0≤outsideLawMass S q := Finset.sum_nonneg (fun x _ => hq x)
  have hInside := unit_interpolation_coordinate_bound S p q L hp hq hInterpolation hBound hMoment
  have hPoint (x : α) : |q x-p x|≤outsideLawMass S q := by
    by_cases hx : x∈S
    · exact hInside ⟨x,hx⟩
    · rw [hp x hx,sub_zero,abs_of_nonneg (hq x)]
      exact Finset.single_le_sum (fun y _ => hq y) (Finset.mem_compl.mpr hx)
  constructor
  · exact (pi_norm_le_iff_of_nonneg hE).mpr (fun x => by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hPoint x)
  · rw [← Finset.sum_add_sum_compl S (fun x => |q x-p x|)]
    have hS : (∑ x∈S,|q x-p x|)≤(S.card : ℝ)*outsideLawMass S q := by
      calc
        _≤∑ _∈S,outsideLawMass S q := Finset.sum_le_sum (fun x hx => hInside ⟨x,hx⟩)
        _=_ := by simp
    have hOut : (∑ x∈Sᶜ,|q x-p x|)=outsideLawMass S q := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hp x (Finset.mem_compl.mp hx),sub_zero,abs_of_nonneg (hq x)]
    rw [hOut]
    nlinarith

theorem unit_interpolation_collision_bound {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : 0<S.card) (p q : α → ℝ) (L : S → α → ℝ)
    (hp : ∀ x,p x=if x∈S then 1/(S.card : ℝ) else 0) (hMassP : ∑ x,p x=1)
    (hq : ∀ x,0≤q x) (hMassQ : ∑ x,q x=1)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (hMoment : ∀ s,∑ x,q x*L s x=∑ x,p x*L s x) :
    ‖q-p‖≤outsideLawMass S q ∧
      collision q-collision p≤outsideLawMass S q*
        (-2/(S.card : ℝ)+((S.card : ℝ)+1)*‖q-p‖) := by
  classical
  have hPout (x : α) (hx : x∉S) : p x=0 := by simp [hp,hx]
  obtain ⟨hNorm,hL1⟩ := unit_interpolation_norm_bounds S p q L hPout hq hInterpolation hBound hMoment
  have hOutsideP : (∑ x∈Sᶜ,p x)=0 := Finset.sum_eq_zero (fun x hx => hPout x (Finset.mem_compl.mp hx))
  have hSumS : (∑ x∈S,(q x-p x))= -outsideLawMass S q := by
    have hP := Finset.sum_add_sum_compl S p
    have hQ := Finset.sum_add_sum_compl S q
    rw [hMassP,hOutsideP,add_zero] at hP
    rw [hMassQ] at hQ
    change (∑ x∈S,q x)+(outsideLawMass S q)=1 at hQ
    rw [Finset.sum_sub_distrib,hP]
    linarith
  have hDot : lawOverlap p (q-p)= -(outsideLawMass S q)/(S.card : ℝ) := by
    unfold lawOverlap
    have hSum : (∑ x,p x*(q-p) x)=∑ x∈S,(1/(S.card : ℝ))*(q x-p x) := by
      have hRestrict : (∑ x∈S,p x*(q-p) x)=(∑ x,p x*(q-p) x) :=
        Finset.sum_subset (Finset.subset_univ S) (fun x _ hx => by rw [hPout x hx,zero_mul])
      rw [← hRestrict]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [hp x,if_pos hx,Pi.sub_apply]
    rw [hSum,← Finset.mul_sum,hSumS]
    ring
  have hQuadratic : collision (q-p)≤‖q-p‖*(∑ x,|q x-p x|) := by
    unfold collision
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hAbs : |q x-p x|≤‖q-p‖ := by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (q-p) x
    have hMul := mul_le_mul_of_nonneg_right hAbs (abs_nonneg (q x-p x))
    simpa only [Pi.sub_apply,← pow_two,sq_abs] using hMul
  have hQuadBound := mul_le_mul_of_nonneg_left hL1 (norm_nonneg (q-p))
  have hInc := collision_direction_expansion p (q-p) 1
  have hFun : (fun x => p x+1*(q-p) x)=q := by funext x;simp
  rw [hFun,hDot] at hInc
  simp only [one_mul,one_pow,mul_one] at hInc
  refine ⟨hNorm,?_⟩
  have hDiv : -(outsideLawMass S q)/(S.card : ℝ)= -(outsideLawMass S q)*(1/(S.card : ℝ)) := by ring
  rw [hDiv] at hInc
  have hRhs : outsideLawMass S q*(-2/(S.card : ℝ)+((S.card : ℝ)+1)*‖q-p‖)=
      -2*outsideLawMass S q*(1/(S.card : ℝ))+‖q-p‖*(((S.card : ℝ)+1)*outsideLawMass S q) := by ring
  rw [hRhs]
  nlinarith

theorem unit_interpolation_strict_radius {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : 0<S.card) (p q : α → ℝ) (L : S → α → ℝ)
    (hp : ∀ x,p x=if x∈S then 1/(S.card : ℝ) else 0) (hMassP : ∑ x,p x=1)
    (hq : ∀ x,0≤q x) (hMassQ : ∑ x,q x=1)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (hMoment : ∀ s,∑ x,q x*L s x=∑ x,p x*L s x)
    (hqp : q≠p) (hClose : ‖q-p‖<2/((S.card : ℝ)*((S.card : ℝ)+1))) :
    collision q<collision p := by
  have hm : (0 : ℝ)<S.card := by exact_mod_cast hS
  have hm1 : 0<(S.card : ℝ)+1 := by positivity
  obtain ⟨hNorm,hCollision⟩ := unit_interpolation_collision_bound S hS p q L hp hMassP hq hMassQ hInterpolation hBound hMoment
  have hE : 0<outsideLawMass S q := (norm_pos_iff.mpr (sub_ne_zero.mpr hqp)).trans_le hNorm
  have hScale := mul_lt_mul_of_pos_left hClose hm1
  have hCancel : ((S.card : ℝ)+1)*(2/((S.card : ℝ)*((S.card : ℝ)+1)))=2/(S.card : ℝ) := by
    field_simp
  rw [hCancel] at hScale
  have hNeg : -2/(S.card : ℝ)+((S.card : ℝ)+1)*‖q-p‖<0 := by rw [neg_div];linarith
  have hProd := mul_neg_of_pos_of_neg hE hNeg
  linarith

theorem unit_interpolation_shell_drop {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : 0<S.card) (p q : α → ℝ) (L : S → α → ℝ)
    (hp : ∀ x,p x=if x∈S then 1/(S.card : ℝ) else 0) (hMassP : ∑ x,p x=1)
    (hq : ∀ x,0≤q x) (hMassQ : ∑ x,q x=1)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (hMoment : ∀ s,∑ x,q x*L s x=∑ x,p x*L s x)
    (hDistance : ‖q-p‖=1/((S.card : ℝ)*((S.card : ℝ)+1))) :
    collision q≤collision p-1/((S.card : ℝ)^2*((S.card : ℝ)+1)) := by
  have hm : (0 : ℝ)<S.card := by exact_mod_cast hS
  have hm1 : 0<(S.card : ℝ)+1 := by positivity
  obtain ⟨hNorm,hCollision⟩ := unit_interpolation_collision_bound S hS p q L hp hMassP hq hMassQ hInterpolation hBound hMoment
  have hBracket : -2/(S.card : ℝ)+((S.card : ℝ)+1)*(1/((S.card : ℝ)*((S.card : ℝ)+1)))= -1/(S.card : ℝ) := by
    field_simp
    <;> ring
  rw [hDistance] at hNorm hCollision
  rw [hBracket] at hCollision
  have hMul := mul_le_mul_of_nonneg_right hNorm (show 0≤1/(S.card : ℝ) by positivity)
  have hGap : (1/((S.card : ℝ)*((S.card : ℝ)+1)))*(1/(S.card : ℝ))=
      1/((S.card : ℝ)^2*((S.card : ℝ)+1)) := by
    field_simp
    <;> ring
  rw [hGap] at hMul
  rw [neg_div,mul_neg] at hCollision
  linarith

theorem unit_interpolation_path_barrier {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : 0<S.card) (p : α → ℝ) (L : S → α → ℝ)
    (hp : ∀ x,p x=if x∈S then 1/(S.card : ℝ) else 0) (hMassP : ∑ x,p x=1)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (path : ℝ → (α → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1))
    (hStart : path 0=p) (hEnd : collision p<collision (path 1))
    (hLaw : ∀ t∈Set.Icc (0 : ℝ) 1,(∀ x,0≤path t x) ∧ (∑ x,path t x)=1 ∧
      ∀ s,∑ x,path t x*L s x=∑ x,p x*L s x) :
    ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤collision p-1/((S.card : ℝ)^2*((S.card : ℝ)+1)) := by
  have hm : (0 : ℝ)<S.card := by exact_mod_cast hS
  have hm1 : 0<(S.card : ℝ)+1 := by positivity
  have hEndpointNe : path 1≠p := by intro h;rw [h] at hEnd;exact lt_irrefl _ hEnd
  have hLawEnd := hLaw 1 (by norm_num)
  have hFar : 2/((S.card : ℝ)*((S.card : ℝ)+1))≤‖path 1-p‖ := by
    apply le_of_not_gt
    intro hClose
    have hDrop := unit_interpolation_strict_radius S hS p (path 1) L hp hMassP
      hLawEnd.1 hLawEnd.2.1 hInterpolation hBound hLawEnd.2.2 hEndpointNe hClose
    linarith
  let ρ := 1/((S.card : ℝ)*((S.card : ℝ)+1))
  have hρ : 0<ρ := by dsimp only [ρ];positivity
  have hρFar : ρ≤‖path 1-p‖ := by
    have hTwo : 2/((S.card : ℝ)*((S.card : ℝ)+1))=2*ρ := by dsimp only [ρ];ring
    rw [hTwo] at hFar
    linarith
  have hDistanceContinuous : ContinuousOn (fun t : ℝ => ‖path t-p‖) (Set.Icc 0 1) :=
    (hContinuous.sub continuousOn_const).norm
  have hTarget : ρ∈Set.Icc ‖path 0-p‖ ‖path 1-p‖ := by
    rw [hStart,sub_self,norm_zero]
    exact ⟨hρ.le,hρFar⟩
  obtain ⟨t,ht,hDistance⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num) hDistanceContinuous hTarget
  have hLawT := hLaw t ht
  refine ⟨t,ht,?_⟩
  exact unit_interpolation_shell_drop S hS p (path t) L hp hMassP hLawT.1 hLawT.2.1
    hInterpolation hBound hLawT.2.2 hDistance

end
end EntropyDesigns.Concentration.Interpolation
