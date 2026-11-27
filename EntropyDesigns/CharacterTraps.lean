/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Modified imports for bounded compilation; mathematical statements and proof bodies are unchanged. -/
module
public import EntropyDesigns.SupportReduction
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Order.IntermediateValue
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
public import EntropyDesigns.TrapOptimizers
public import EntropyDesigns.SupportRestriction
public import Mathlib.Topology.Order.LocalExtr
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns
open Filter
open scoped Topology
noncomputable section

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



theorem unit_interpolation_vertex {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (p : α → ℝ) (L : S → α → ℝ) (P : Set (α → ℝ))
    (hpP : p∈P) (hp : ∀ x,x∉S → p x=0)
    (hInterpolation : ∀ s : S,∀ x∈S,L s x=if x=s.val then 1 else 0)
    (hBound : ∀ s x,|L s x|≤1)
    (hNonneg : ∀ q∈P,∀ x,0≤q x)
    (hMoment : ∀ q∈P,∀ s,∑ x,q x*L s x=∑ x,p x*L s x) :
    p∈Set.extremePoints ℝ P := by
  classical
  refine ⟨hpP,?_⟩
  intro q hq r hr hSegment
  obtain ⟨a,b,ha,hb,hab,hCombo⟩ := hSegment
  have hOutside (x : α) (hx : x∉S) : q x=0 := by
    have hh := congrFun hCombo x
    change a*q x+b*r x=p x at hh
    rw [hp x hx] at hh
    have hQ := hNonneg q hq x
    have hR := hNonneg r hr x
    have hRmul := mul_nonneg hb.le hR
    have hMul : a*q x=0 := by nlinarith
    exact (mul_eq_zero.mp hMul).resolve_left ha.ne'
  have hOutsideMass : outsideLawMass S q=0 := Finset.sum_eq_zero
    (fun x hx => hOutside x (Finset.mem_compl.mp hx))
  have hNorm := (unit_interpolation_norm_bounds S p q L hp (hNonneg q hq) hInterpolation hBound (hMoment q hq)).1
  rw [hOutsideMass] at hNorm
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hNorm (norm_nonneg _)))

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



def trapFirstCharacter {s : ℕ} (S : Finset (Fin s)) (x : TrapCoordinate s → Bool) : ℤ :=
  if h : S=∅ then 1 else bitSign (x ⟨Sum.inl S,fun he => h (Sum.inl.inj he)⟩)

def trapSecondCharacter {s : ℕ} (S : Finset (Fin s)) (x : TrapCoordinate s → Bool) : ℤ :=
  if S=∅ then 1 else bitSign (x ⟨Sum.inr S,by intro h;cases h⟩)

theorem trapFirstCharacter_sign {s : ℕ} (S : Finset (Fin s)) (x : TrapCoordinate s → Bool) :
    trapFirstCharacter S x=1 ∨ trapFirstCharacter S x= -1 := by
  unfold trapFirstCharacter
  split_ifs
  · exact Or.inl rfl
  · exact bitSign_sign _

theorem trapSecondCharacter_sign {s : ℕ} (S : Finset (Fin s)) (x : TrapCoordinate s → Bool) :
    trapSecondCharacter S x=1 ∨ trapSecondCharacter S x= -1 := by
  unfold trapSecondCharacter
  split_ifs
  · exact Or.inl rfl
  · exact bitSign_sign _

theorem trapFirstCharacter_code {s : ℕ} (e S : Finset (Fin s)) (u : (Fin s → Bool)×(Fin s → Bool)) :
    trapFirstCharacter S (trapCode e u)=walshChar S u.1 := by
  unfold trapFirstCharacter
  split_ifs with h
  · subst S;simp [walshChar]
  · rw [trapCode_sign]
    rfl

theorem trapSecondCharacter_code {s : ℕ} (e S : Finset (Fin s)) (u : (Fin s → Bool)×(Fin s → Bool)) :
    trapSecondCharacter S (trapCode e u)=walshChar S u.2 := by
  unfold trapSecondCharacter
  split_ifs with h
  · subst S;simp [walshChar]
  · rw [trapCode_sign]
    simp [trapRow,h]

theorem trap_first_character_mean {s : ℕ} (q : (TrapCoordinate s → Bool) → ℝ)
    (hq : observedFeasible q) (S : Finset (Fin s)) :
    (∑ x,q x*(trapFirstCharacter S x : ℝ))=if S=∅ then 1 else 0 := by
  classical
  by_cases hS : S=∅
  · simp [trapFirstCharacter,hS,hq.2.1]
  · simpa only [trapFirstCharacter,dif_neg hS,if_neg hS] using hq.2.2.1 ⟨Sum.inl S,fun he => hS (Sum.inl.inj he)⟩

theorem trap_second_character_mean {s : ℕ} (q : (TrapCoordinate s → Bool) → ℝ)
    (hq : observedFeasible q) (S : Finset (Fin s)) :
    (∑ x,q x*(trapSecondCharacter S x : ℝ))=if S=∅ then 1 else 0 := by
  classical
  by_cases hS : S=∅
  · simp [trapSecondCharacter,hS,hq.2.1]
  · simpa only [trapSecondCharacter,if_neg hS] using hq.2.2.1 ⟨Sum.inr S,by intro h;cases h⟩

theorem trap_character_cross_moment {s : ℕ} (q : (TrapCoordinate s → Bool) → ℝ)
    (hq : observedFeasible q) (S T : Finset (Fin s)) :
    (∑ x,q x*(trapFirstCharacter S x : ℝ)*(trapSecondCharacter T x : ℝ))=
      if S=∅ ∧ T=∅ then 1 else 0 := by
  classical
  by_cases hS : S=∅
  · subst S
    simpa [trapFirstCharacter] using trap_second_character_mean q hq T
  · by_cases hT : T=∅
    · subst T
      simpa [trapSecondCharacter,hS] using trap_first_character_mean q hq S
    · let i : TrapCoordinate s := ⟨Sum.inl S,fun he => hS (Sum.inl.inj he)⟩
      let j : TrapCoordinate s := ⟨Sum.inr T,by intro h;cases h⟩
      have hij : i≠j := by intro h;have he := congrArg Subtype.val h;cases he
      have hh := hq.2.2.2 i j hij
      simpa [trapFirstCharacter,trapSecondCharacter,hS,hT,i,j] using hh


def seedTrapInterpolation {s : ℕ} (u : (Fin s → Bool)×(Fin s → Bool))
    (x : TrapCoordinate s → Bool) : ℝ :=
  (1/(2 : ℝ)^(2*s))*(∑ S : Finset (Fin s),(walshChar S u.1 : ℝ)*(trapFirstCharacter S x : ℝ))*
    (∑ T : Finset (Fin s),(walshChar T u.2 : ℝ)*(trapSecondCharacter T x : ℝ))

theorem seedTrapInterpolation_bounded {s : ℕ} (u : (Fin s → Bool)×(Fin s → Bool))
    (x : TrapCoordinate s → Bool) : |seedTrapInterpolation u x|≤1 := by
  have hAbs (z : ℤ) (hz : z=1 ∨ z= -1) : |(z : ℝ)|=1 := by rcases hz with rfl|rfl <;> norm_num
  have hFirst : |∑ S : Finset (Fin s),(walshChar S u.1 : ℝ)*(trapFirstCharacter S x : ℝ)|≤(2 : ℝ)^s := by
    calc
      _≤∑ S : Finset (Fin s),|(walshChar S u.1 : ℝ)*(trapFirstCharacter S x : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _=_ := by simp only [abs_mul,hAbs _ (walshChar_sign _ _),hAbs _ (trapFirstCharacter_sign _ _),one_mul];simp
  have hSecond : |∑ T : Finset (Fin s),(walshChar T u.2 : ℝ)*(trapSecondCharacter T x : ℝ)|≤(2 : ℝ)^s := by
    calc
      _≤∑ T : Finset (Fin s),|(walshChar T u.2 : ℝ)*(trapSecondCharacter T x : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _=_ := by simp only [abs_mul,hAbs _ (walshChar_sign _ _),hAbs _ (trapSecondCharacter_sign _ _),one_mul];simp
  have hProd := mul_le_mul hFirst hSecond (abs_nonneg _) (show 0≤(2 : ℝ)^s by positivity)
  have hm : (2 : ℝ)^(2*s)=(2 : ℝ)^s*(2 : ℝ)^s := by rw [two_mul,pow_add]
  calc
    |seedTrapInterpolation u x|=(1/(2 : ℝ)^(2*s))*
        (|∑ S : Finset (Fin s),(walshChar S u.1 : ℝ)*(trapFirstCharacter S x : ℝ)| *
         |∑ T : Finset (Fin s),(walshChar T u.2 : ℝ)*(trapSecondCharacter T x : ℝ)|) := by
      rw [seedTrapInterpolation,abs_mul,abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤1/(2 : ℝ)^(2*s))]
      ring
    _≤(1/(2 : ℝ)^(2*s))*((2 : ℝ)^s*(2 : ℝ)^s) := mul_le_mul_of_nonneg_left hProd (by positivity)
    _=1 := by rw [hm];field_simp

theorem seedTrapInterpolation_code {s : ℕ} (e : Finset (Fin s))
    (u v : (Fin s → Bool)×(Fin s → Bool)) :
    seedTrapInterpolation u (trapCode e v)=if v=u then 1 else 0 := by
  unfold seedTrapInterpolation
  simp_rw [trapFirstCharacter_code,trapSecondCharacter_code]
  rw [walshChar_real_dual_orthogonality,walshChar_real_dual_orthogonality]
  have hm : (2 : ℝ)^(2*s)=(2 : ℝ)^s*(2 : ℝ)^s := by rw [two_mul,pow_add]
  by_cases h1 : u.1=v.1
  · by_cases h2 : u.2=v.2
    · have heq : v=u := Prod.ext h1.symm h2.symm
      simp only [h1,h2,heq,ite_true]
      rw [hm]
      field_simp
    · have hne : v≠u := fun h => h2 (congrArg Prod.snd h.symm)
      simp [h1,h2,hne]
  · have hne : v≠u := fun h => h1 (congrArg Prod.fst h.symm)
    simp [h1,hne]



theorem seedTrapInterpolation_moment {s : ℕ} (q : (TrapCoordinate s → Bool) → ℝ)
    (hq : observedFeasible q) (u : (Fin s → Bool)×(Fin s → Bool)) :
    (∑ x,q x*seedTrapInterpolation u x)=1/(2 : ℝ)^(2*s) := by
  classical
  calc
    _=∑ x,∑ S : Finset (Fin s),∑ T : Finset (Fin s),
        (1/(2 : ℝ)^(2*s))*((walshChar S u.1 : ℝ)*(walshChar T u.2 : ℝ))*
          (q x*(trapFirstCharacter S x : ℝ)*(trapSecondCharacter T x : ℝ)) := by
      simp only [seedTrapInterpolation,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl;intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro S hS
      apply Finset.sum_congr rfl;intro T hT
      ring
    _=(1/(2 : ℝ)^(2*s))*(∑ S : Finset (Fin s),∑ T : Finset (Fin s),
        ((walshChar S u.1 : ℝ)*(walshChar T u.2 : ℝ))*
          (∑ x,q x*(trapFirstCharacter S x : ℝ)*(trapSecondCharacter T x : ℝ))) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro S hS
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro T hT
      apply Finset.sum_congr rfl;intro x hx
      ring
    _=_ := by
      simp_rw [trap_character_cross_moment q hq]
      simp [ite_and,walshChar]



noncomputable def trapSupportSeed {s : ℕ} (e : Finset (Fin s))
    (x : activeSupport (trapLaw e)) : (Fin s → Bool)×(Fin s → Bool) :=
  Classical.choose ((trapLaw_nonzero_iff e x.val).mp (by
    simpa only [activeSupport,Finset.mem_filter,Finset.mem_univ,true_and] using x.property))

theorem trapSupportSeed_code {s : ℕ} (e : Finset (Fin s)) (x : activeSupport (trapLaw e)) :
    trapCode e (trapSupportSeed e x)=x.val := by
  unfold trapSupportSeed
  exact Classical.choose_spec ((trapLaw_nonzero_iff e x.val).mp (by
    simpa only [activeSupport,Finset.mem_filter,Finset.mem_univ,true_and] using x.property))

noncomputable def trapAtomInterpolation {s : ℕ} (e : Finset (Fin s))
    (x : activeSupport (trapLaw e)) (y : TrapCoordinate s → Bool) : ℝ :=
  seedTrapInterpolation (trapSupportSeed e x) y

theorem trapLaw_observedFeasible {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    observedFeasible (trapLaw e) :=
  ⟨(trapLaw_probability e).1,(trapLaw_probability e).2,trapLaw_mean e he,trapLaw_pair e he⟩

theorem trap_atom_interpolation_delta {s : ℕ} (e : Finset (Fin s))
    (x : activeSupport (trapLaw e)) (y : TrapCoordinate s → Bool) (hy : y∈activeSupport (trapLaw e)) :
    trapAtomInterpolation e x y=if y=x.val then 1 else 0 := by
  classical
  obtain ⟨v,hv⟩ := (trapLaw_nonzero_iff e y).mp (by simpa [activeSupport] using hy)
  have hEq : v=trapSupportSeed e x ↔ y=x.val := by
    constructor
    · intro h
      rw [← hv,h,trapSupportSeed_code]
    · intro h
      apply trapCode_injective e
      rw [hv,trapSupportSeed_code,h]
  unfold trapAtomInterpolation
  have hh := seedTrapInterpolation_code e (trapSupportSeed e x) v
  rw [hv] at hh
  simpa only [hEq] using hh

theorem trap_atom_interpolation_moment {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (q : (TrapCoordinate s → Bool) → ℝ) (hq : observedFeasible q)
    (x : activeSupport (trapLaw e)) :
    (∑ y,q y*trapAtomInterpolation e x y)=(∑ y,trapLaw e y*trapAtomInterpolation e x y) := by
  unfold trapAtomInterpolation
  rw [seedTrapInterpolation_moment q hq,seedTrapInterpolation_moment _ (trapLaw_observedFeasible e he)]

theorem trapLaw_uniform_on_activeSupport {s : ℕ} (e : Finset (Fin s)) :
    ∀ x,trapLaw e x=if x∈activeSupport (trapLaw e) then
      1/((activeSupport (trapLaw e)).card : ℝ) else 0 := by
  classical
  intro x
  have hCard : (activeSupport (trapLaw e)).card=2^(2*s) := trapLaw_support_card e
  by_cases hx : x∈activeSupport (trapLaw e)
  · have hNZ : trapLaw e x≠0 := by simpa only [activeSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    rw [if_pos hx,hCard]
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using (trapLaw_weights e x).resolve_left hNZ
  · have hZero : trapLaw e x=0 := by simpa [activeSupport] using hx
    rw [if_neg hx,hZero]

theorem character_trap_vertex_and_radius {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty) :
    observedFeasible (trapLaw e) ∧
    trapLaw e∈Set.extremePoints ℝ {q | observedFeasible q} ∧
    (∀ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q → q≠trapLaw e →
      ‖q-trapLaw e‖<2/((2 : ℝ)^(2*s)*((2 : ℝ)^(2*s)+1)) → collision q<collision (trapLaw e)) ∧
    IsLocalMaxOn collision {q | observedFeasible q} (trapLaw e) := by
  classical
  let S := activeSupport (trapLaw e)
  have hCard : S.card=2^(2*s) := trapLaw_support_card e
  have hPos : 0<S.card := by rw [hCard];positivity
  have hP := trapLaw_observedFeasible e he
  have hBound (x : S) (y : TrapCoordinate s → Bool) : |trapAtomInterpolation e x y|≤1 := seedTrapInterpolation_bounded _ _
  have hVertex := unit_interpolation_vertex S (trapLaw e) (trapAtomInterpolation e) {q | observedFeasible q} hP
    (fun x hx => by simpa only [S,activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hx)
    (trap_atom_interpolation_delta e) hBound (fun q hq => hq.1) (trap_atom_interpolation_moment e he)
  have hStrict (q : (TrapCoordinate s → Bool) → ℝ) (hq : observedFeasible q) (hqp : q≠trapLaw e)
      (hClose : ‖q-trapLaw e‖<2/((2 : ℝ)^(2*s)*((2 : ℝ)^(2*s)+1))) : collision q<collision (trapLaw e) := by
    apply unit_interpolation_strict_radius S hPos (trapLaw e) q (trapAtomInterpolation e)
      (trapLaw_uniform_on_activeSupport e) hP.2.1 hq.1 hq.2.1 (trap_atom_interpolation_delta e) hBound
      (trap_atom_interpolation_moment e he q hq) hqp
    simpa only [hCard,Nat.cast_pow,Nat.cast_ofNat] using hClose
  refine ⟨hP,hVertex,hStrict,?_⟩
  have hR : 0<2/((2 : ℝ)^(2*s)*((2 : ℝ)^(2*s)+1)) := by positivity
  have hBall : ∀ᶠ q : (TrapCoordinate s → Bool) → ℝ in 𝓝 (trapLaw e),
      ‖q-trapLaw e‖<2/((2 : ℝ)^(2*s)*((2 : ℝ)^(2*s)+1)) := by
    simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds (trapLaw e) hR
  have hMem : ∀ᶠ q in 𝓝[{q | observedFeasible q}] (trapLaw e),observedFeasible q := self_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds hBall,hMem] with q hClose hq
  by_cases hqp : q=trapLaw e
  · subst q;exact le_rfl
  · exact (hStrict q hq hqp hClose).le



theorem character_trap_relative_collision_limit :
    Tendsto (fun s : ℕ => 2/(2 : ℝ)^s) atTop (𝓝 0) := by
  have hp : Tendsto (fun s : ℕ => (1/2 : ℝ)^s) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh := hp.const_mul 2
  simpa only [one_div,inv_pow,div_eq_mul_inv,one_mul,mul_zero] using hh

theorem arbitrarily_poor_character_traps (s : ℕ) (hs : 2≤s) :
    Fintype.card (TrapCoordinate s)=2*2^s-1 ∧ 4∣(Fintype.card (TrapCoordinate s)+1) ∧
    ∃ p : (TrapCoordinate s → Bool) → ℝ,
      observedFeasible p ∧ (activeSupport p).card=2^(2*s) ∧
      (∀ x,p x=0 ∨ p x=1/(2 : ℝ)^(2*s)) ∧
      p∈Set.extremePoints ℝ {q | observedFeasible q} ∧
      IsLocalMaxOn collision {q | observedFeasible q} p ∧
      (∀ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q → q≠p →
        ‖q-p‖<2/((2 : ℝ)^(2*s)*((2 : ℝ)^(2*s)+1)) → collision q<collision p) ∧
      collision p=1/(2 : ℝ)^(2*s) ∧
      (∃ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q ∧ collision q=1/(2*(2 : ℝ)^s)) ∧
      (∀ q : (TrapCoordinate s → Bool) → ℝ,observedFeasible q → collision q≤1/(2*(2 : ℝ)^s)) ∧
      collision p/(1/(2*(2 : ℝ)^s))=2/(2 : ℝ)^s := by
  classical
  let e : Finset (Fin s) := {⟨0,by omega⟩}
  have he : e.Nonempty := Finset.singleton_nonempty _
  obtain ⟨hP,hVertex,hRadius,hLocal⟩ := character_trap_vertex_and_radius e he
  have hCoord := trap_coordinate_card s
  have hPow : 1≤2^s := Nat.one_le_pow s 2 (by omega)
  have hOrder : Fintype.card (TrapCoordinate s)+1=2^(s+1) := by
    rw [hCoord,pow_succ]
    omega
  have hFour : 4∣(Fintype.card (TrapCoordinate s)+1) := by
    rw [hOrder]
    exact (show 4=2^2 by norm_num) ▸ (Nat.pow_dvd_pow 2 (by omega : 2≤s+1))
  refine ⟨hCoord,hFour,trapLaw e,hP,trapLaw_support_card e,trapLaw_weights e,hVertex,hLocal,hRadius,
    trapLaw_collision e,⟨endpointLaw s,(endpointLaw_global_maximum s).1,endpointLaw_collision s⟩,
    (fun q hq => observed_law_collision_cap q hq),?_⟩
  rw [trapLaw_collision]
  have hm : (2 : ℝ)^(2*s)=(2 : ℝ)^s*(2 : ℝ)^s := by rw [two_mul,pow_add]
  rw [hm]
  field_simp

theorem character_trap_path_barrier {s : ℕ} (e : Finset (Fin s)) (he : e.Nonempty)
    (path : ℝ → ((TrapCoordinate s → Bool) → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1))
    (hStart : path 0=trapLaw e) (hEnd : collision (trapLaw e)<collision (path 1))
    (hFeasible : ∀ t∈Set.Icc (0 : ℝ) 1,observedFeasible (path t)) :
    ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤1/(2 : ℝ)^(2*s)-
      1/(((2 : ℝ)^(2*s))^2*((2 : ℝ)^(2*s)+1)) := by
  classical
  let S := activeSupport (trapLaw e)
  have hCard : S.card=2^(2*s) := trapLaw_support_card e
  have hPos : 0<S.card := by rw [hCard];positivity
  have hP := trapLaw_observedFeasible e he
  obtain ⟨t,ht,hBarrier⟩ := unit_interpolation_path_barrier S hPos (trapLaw e) (trapAtomInterpolation e)
    (trapLaw_uniform_on_activeSupport e) hP.2.1 (trap_atom_interpolation_delta e)
    (fun x y => seedTrapInterpolation_bounded _ _) path hContinuous hStart hEnd (by
      intro t ht
      have hq := hFeasible t ht
      exact ⟨hq.1,hq.2.1,trap_atom_interpolation_moment e he (path t) hq⟩)
  refine ⟨t,ht,?_⟩
  simpa only [hCard,Nat.cast_pow,Nat.cast_ofNat,trapLaw_collision] using hBarrier


end
end EntropyDesigns
