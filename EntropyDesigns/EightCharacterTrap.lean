/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.CharacterTraps
public import EntropyDesigns.CollisionLocalMaxima
public import EntropyDesigns.MaskCoverage
public import EntropyDesigns.WalshBlocks
public import EntropyDesigns.HadamardLaws
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
@[expose] public section
set_option maxHeartbeats 2000000
namespace EntropyDesigns
open Filter
open scoped Topology symmDiff
noncomputable section

def eightTrapMasks : Fin 7 → Finset (Fin 4) := ![{0},{1},{0,1},{2},{0,2},{3},{1,3}]

theorem eightTrapMasks_properties : Function.Injective eightTrapMasks ∧ ∀ j,eightTrapMasks j≠∅ := by
  decide +kernel

def eightTrapCode (u : Fin 4 → Bool) : Fin 7 → Bool := fun j => decide (walshChar (eightTrapMasks j) u= -1)

theorem eightTrapCode_sign (u : Fin 4 → Bool) (j : Fin 7) :
    bitSign (eightTrapCode u j)=walshChar (eightTrapMasks j) u := by
  rcases walshChar_sign (eightTrapMasks j) u with h|h <;> simp [eightTrapCode,bitSign,h]

theorem eightTrapCode_injective : Function.Injective eightTrapCode := by decide +kernel

abbrev EightMomentIndex := Unit ⊕ (Fin 7 ⊕ (Fin 7×Fin 7))

def eightMomentMask : EightMomentIndex → Finset (Fin 4) :=
  Sum.elim (fun _ => ∅) (Sum.elim eightTrapMasks (fun ij => eightTrapMasks ij.1 ∆ eightTrapMasks ij.2))

def eightMomentValue (r : EightMomentIndex) (x : Fin 7 → Bool) : ℤ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun i => bitSign (x i)) (fun ij => bitSign (x ij.1)*bitSign (x ij.2))) r

theorem eight_moment_mask_cover : ∀ S : Finset (Fin 4),∃ r : EightMomentIndex,eightMomentMask r=S := by
  decide +kernel

noncomputable def eightMomentRepresentative (S : Finset (Fin 4)) : EightMomentIndex :=
  Classical.choose (eight_moment_mask_cover S)

theorem eightMomentRepresentative_spec (S : Finset (Fin 4)) : eightMomentMask (eightMomentRepresentative S)=S :=
  Classical.choose_spec (eight_moment_mask_cover S)

theorem eightMomentValue_sign (r : EightMomentIndex) (x : Fin 7 → Bool) :
    eightMomentValue r x=1 ∨ eightMomentValue r x= -1 := by
  rcases r with u|i|⟨i,j⟩
  · exact Or.inl rfl
  · exact bitSign_sign _
  · rcases bitSign_sign (x i) with h|h <;> rcases bitSign_sign (x j) with h'|h' <;>
      simp [eightMomentValue,h,h']

theorem eightMomentValue_code (r : EightMomentIndex) (u : Fin 4 → Bool) :
    eightMomentValue r (eightTrapCode u)=walshChar (eightMomentMask r) u := by
  rcases r with z|i|⟨i,j⟩
  · simp [eightMomentValue,eightMomentMask,walshChar]
  · exact eightTrapCode_sign u i
  · simpa only [eightMomentValue,eightMomentMask,Sum.elim_inr,Sum.elim_inl,eightTrapCode_sign] using (walshChar_product (eightTrapMasks i) (eightTrapMasks j) u).symm

theorem eightMomentValue_expectation (q : (Fin 7 → Bool) → ℝ) (hq : cubeProbabilityFeasible q)
    (r : EightMomentIndex) :
    (∑ x,q x*(eightMomentValue r x : ℝ))=if eightMomentMask r=∅ then 1 else 0 := by
  rcases r with z|i|⟨i,j⟩
  · simpa [eightMomentValue,eightMomentMask] using hq.2.1
  · simpa [eightMomentValue,eightMomentMask,eightTrapMasks_properties.2 i] using hq.2.2.1 i
  · by_cases hij : i=j
    · subst j
      have hs (x : Fin 7 → Bool) : bitSign (x i)*bitSign (x i)=(1 : ℤ) := by cases x i <;> norm_num [bitSign]
      simpa [eightMomentValue,eightMomentMask,hs] using hq.2.1
    · have hMasks : eightTrapMasks i≠eightTrapMasks j := fun h => hij (eightTrapMasks_properties.1 h)
      have hPair := hq.2.2.2 i j hij
      simpa [eightMomentValue,eightMomentMask,hMasks,Finset.symmDiff_eq_empty,mul_assoc] using hPair


theorem eightTrapMasks_binary_codes : ∀ j : Fin 7,
    (∑ i∈eightTrapMasks j,2^i.val)=(![1,2,3,4,5,8,10] : Fin 7 → ℕ) j := by decide +kernel

noncomputable def eightSeedInterpolation (u : Fin 4 → Bool) (x : Fin 7 → Bool) : ℝ :=
  (1/16 : ℝ)*∑ S : Finset (Fin 4),(walshChar S u : ℝ)*(eightMomentValue (eightMomentRepresentative S) x : ℝ)

theorem eightSeedInterpolation_bounded (u : Fin 4 → Bool) (x : Fin 7 → Bool) :
    |eightSeedInterpolation u x|≤1 := by
  have hAbs (z : ℤ) (hz : z=1 ∨ z= -1) : |(z : ℝ)|=1 := by rcases hz with rfl|rfl <;> norm_num
  have hSum : |∑ S : Finset (Fin 4),(walshChar S u : ℝ)*(eightMomentValue (eightMomentRepresentative S) x : ℝ)|≤16 := by
    calc
      _≤∑ S : Finset (Fin 4),|(walshChar S u : ℝ)*(eightMomentValue (eightMomentRepresentative S) x : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _=16 := by simp [abs_mul,hAbs _ (walshChar_sign _ _),hAbs _ (eightMomentValue_sign _ _)]
  rw [eightSeedInterpolation,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/16)]
  nlinarith

theorem eightSeedInterpolation_code (u v : Fin 4 → Bool) :
    eightSeedInterpolation u (eightTrapCode v)=if v=u then 1 else 0 := by
  unfold eightSeedInterpolation
  simp_rw [eightMomentValue_code,eightMomentRepresentative_spec]
  rw [walshChar_real_dual_orthogonality]
  by_cases huv : u=v <;> norm_num [huv,eq_comm]

theorem eightSeedInterpolation_moment (q : (Fin 7 → Bool) → ℝ) (hq : cubeProbabilityFeasible q)
    (u : Fin 4 → Bool) : (∑ x,q x*eightSeedInterpolation u x)=(1/16 : ℝ) := by
  classical
  calc
    _=(1/16 : ℝ)*∑ S : Finset (Fin 4),(walshChar S u : ℝ)*
        (∑ x,q x*(eightMomentValue (eightMomentRepresentative S) x : ℝ)) := by
      simp only [eightSeedInterpolation,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl;intro S hS
      apply Finset.sum_congr rfl;intro x hx
      ring
    _=_ := by
      simp_rw [eightMomentValue_expectation q hq,eightMomentRepresentative_spec]
      simp [mul_ite,walshChar]



noncomputable def eightTrapLaw : (Fin 7 → Bool) → ℝ := pushLaw eightTrapCode (fun _ : Fin 4 → Bool => (1/16 : ℝ))

theorem eightTrapLaw_probability : (∀ x,0≤eightTrapLaw x) ∧ (∑ x,eightTrapLaw x)=1 := by
  classical
  constructor
  · exact pushLaw_nonneg _ _ (fun _ => by norm_num)
  · rw [eightTrapLaw,pushLaw_mass]
    norm_num

theorem eightTrapLaw_weights (x : Fin 7 → Bool) : eightTrapLaw x=0 ∨ eightTrapLaw x=(1/16 : ℝ) := by
  exact pushLaw_injective_weights _ eightTrapCode_injective _ _ (fun _ => rfl) x

theorem eightTrapLaw_support_card : (activeSupport eightTrapLaw).card=16 := by
  exact support_card_of_uniform_weights eightTrapLaw 16 (by norm_num) eightTrapLaw_probability.2 eightTrapLaw_weights

theorem eightTrapLaw_nonzero_iff (x : Fin 7 → Bool) : eightTrapLaw x≠0 ↔ ∃ u,eightTrapCode u=x := by
  classical
  constructor
  · intro hx
    by_contra h
    have hNot (u : Fin 4 → Bool) : eightTrapCode u≠x := fun hu => h ⟨u,hu⟩
    have hZero : eightTrapLaw x=0 := by simp [eightTrapLaw,pushLaw,hNot]
    exact hx hZero
  · rintro ⟨u,rfl⟩
    change pushLaw eightTrapCode (fun _ : Fin 4 → Bool => (1/16 : ℝ)) (eightTrapCode u)≠0
    rw [pushLaw_injective_value _ eightTrapCode_injective]
    norm_num

theorem eightTrapLaw_feasible : cubeProbabilityFeasible eightTrapLaw := by
  refine ⟨eightTrapLaw_probability.1,eightTrapLaw_probability.2,?_,?_⟩
  · intro i
    change (∑ x,pushLaw eightTrapCode (fun _ : Fin 4 → Bool => (1/16 : ℝ)) x*(bitSign (x i) : ℝ))=0
    rw [pushLaw_moment]
    simp_rw [eightTrapCode_sign]
    rw [← Finset.mul_sum,walshChar_real_sum_zero _ (Finset.nonempty_iff_ne_empty.mpr (eightTrapMasks_properties.2 i)),mul_zero]
  · intro i j hij
    simp_rw [mul_assoc]
    change (∑ x,pushLaw eightTrapCode (fun _ : Fin 4 → Bool => (1/16 : ℝ)) x*
      ((bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)))=0
    rw [pushLaw_moment]
    simp_rw [eightTrapCode_sign]
    rw [← Finset.mul_sum,walshChar_real_orthogonality]
    have hMasks : eightTrapMasks i≠eightTrapMasks j := fun h => hij (eightTrapMasks_properties.1 h)
    simp [hMasks]

theorem eightTrapLaw_collision : collision eightTrapLaw=(1/16 : ℝ) :=
  (entropy_of_uniform_weights eightTrapLaw (by norm_num : (0 : ℝ)<16) eightTrapLaw_probability.2 eightTrapLaw_weights).1

noncomputable def eightSupportSeed (x : activeSupport eightTrapLaw) : Fin 4 → Bool :=
  Classical.choose ((eightTrapLaw_nonzero_iff x.val).mp (by simpa only [activeSupport,Finset.mem_filter,Finset.mem_univ,true_and] using x.property))

theorem eightSupportSeed_code (x : activeSupport eightTrapLaw) : eightTrapCode (eightSupportSeed x)=x.val := by
  unfold eightSupportSeed
  exact Classical.choose_spec ((eightTrapLaw_nonzero_iff x.val).mp (by simpa only [activeSupport,Finset.mem_filter,Finset.mem_univ,true_and] using x.property))

noncomputable def eightAtomInterpolation (x : activeSupport eightTrapLaw) (y : Fin 7 → Bool) : ℝ :=
  eightSeedInterpolation (eightSupportSeed x) y

theorem eight_atom_interpolation_delta (x : activeSupport eightTrapLaw) (y : Fin 7 → Bool)
    (hy : y∈activeSupport eightTrapLaw) : eightAtomInterpolation x y=if y=x.val then 1 else 0 := by
  classical
  obtain ⟨v,hv⟩ := (eightTrapLaw_nonzero_iff y).mp (by simpa [activeSupport] using hy)
  have hEq : v=eightSupportSeed x ↔ y=x.val := by
    constructor
    · intro h;rw [← hv,h,eightSupportSeed_code]
    · intro h;apply eightTrapCode_injective;rw [hv,eightSupportSeed_code,h]
  unfold eightAtomInterpolation
  have hh := eightSeedInterpolation_code (eightSupportSeed x) v
  rw [hv] at hh
  simpa only [hEq] using hh

theorem eight_atom_interpolation_moment (q : (Fin 7 → Bool) → ℝ) (hq : cubeProbabilityFeasible q)
    (x : activeSupport eightTrapLaw) :
    (∑ y,q y*eightAtomInterpolation x y)=(∑ y,eightTrapLaw y*eightAtomInterpolation x y) := by
  unfold eightAtomInterpolation
  rw [eightSeedInterpolation_moment q hq,eightSeedInterpolation_moment _ eightTrapLaw_feasible]

theorem eightTrapLaw_uniform_on_activeSupport :
    ∀ x,eightTrapLaw x=if x∈activeSupport eightTrapLaw then
      1/((activeSupport eightTrapLaw).card : ℝ) else 0 := by
  classical
  intro x
  by_cases hx : x∈activeSupport eightTrapLaw
  · have hNZ : eightTrapLaw x≠0 := by simpa [activeSupport] using hx
    rw [if_pos hx,eightTrapLaw_support_card]
    exact (eightTrapLaw_weights x).resolve_left hNZ
  · have hZero : eightTrapLaw x=0 := by simpa [activeSupport] using hx
    rw [if_neg hx,hZero]



theorem order_eight_character_trap :
    (∀ j : Fin 7,(∑ i∈eightTrapMasks j,2^i.val)=(![1,2,3,4,5,8,10] : Fin 7 → ℕ) j) ∧
    cubeProbabilityFeasible eightTrapLaw ∧ (activeSupport eightTrapLaw).card=16 ∧
    (∀ x,eightTrapLaw x=0 ∨ eightTrapLaw x=(1/16 : ℝ)) ∧ collision eightTrapLaw=(1/16 : ℝ) ∧
    eightTrapLaw∈Set.extremePoints ℝ {q | cubeProbabilityFeasible q} ∧
    IsLocalMaxOn collision {q | cubeProbabilityFeasible q} eightTrapLaw ∧
    (∀ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q → q≠eightTrapLaw →
      ‖q-eightTrapLaw‖<(1/136 : ℝ) → collision q<collision eightTrapLaw) ∧
    (∃ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ)) ∧
    (∀ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q → collision q≤(1/8 : ℝ)) := by
  classical
  let S := activeSupport eightTrapLaw
  have hPos : 0<S.card := by change 0<(activeSupport eightTrapLaw).card;rw [eightTrapLaw_support_card];norm_num
  have hBound (x : S) (y : Fin 7 → Bool) : |eightAtomInterpolation x y|≤1 := eightSeedInterpolation_bounded _ _
  have hVertex := unit_interpolation_vertex S eightTrapLaw eightAtomInterpolation {q | cubeProbabilityFeasible q}
    eightTrapLaw_feasible (fun x hx => by simpa [S,activeSupport] using hx)
    eight_atom_interpolation_delta hBound (fun q hq => hq.1) eight_atom_interpolation_moment
  have hStrict (q : (Fin 7 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) (hqp : q≠eightTrapLaw)
      (hClose : ‖q-eightTrapLaw‖<(1/136 : ℝ)) : collision q<collision eightTrapLaw := by
    apply unit_interpolation_strict_radius S hPos eightTrapLaw q eightAtomInterpolation
      eightTrapLaw_uniform_on_activeSupport eightTrapLaw_probability.2 hq.1 hq.2.1
      eight_atom_interpolation_delta hBound (eight_atom_interpolation_moment q hq) hqp
    simpa only [S,eightTrapLaw_support_card,Nat.cast_ofNat,show (2 : ℝ)/(16*(16+1))=1/136 by norm_num] using hClose
  have hLocal : IsLocalMaxOn collision {q | cubeProbabilityFeasible q} eightTrapLaw := by
    have hBall : ∀ᶠ q : (Fin 7 → Bool) → ℝ in 𝓝 eightTrapLaw,‖q-eightTrapLaw‖<(1/136 : ℝ) := by
      simpa only [Filter.Eventually,Metric.ball,dist_eq_norm] using Metric.ball_mem_nhds eightTrapLaw (by norm_num : (0 : ℝ)<1/136)
    have hMem : ∀ᶠ q in 𝓝[{q | cubeProbabilityFeasible q}] eightTrapLaw,cubeProbabilityFeasible q := self_mem_nhdsWithin
    filter_upwards [nhdsWithin_le_nhds hBall,hMem] with q hClose hq
    by_cases hqp : q=eightTrapLaw
    · subst q;exact le_rfl
    · exact (hStrict q hq hqp hClose).le
  have hGlobal : ∃ q : (Fin 7 → Bool) → ℝ,cubeProbabilityFeasible q ∧ collision q=(1/8 : ℝ) := by
    let e : Finset (Fin 3) ≃ Fin 8 := (Fintype.equivFin _).trans (finCongr (by decide))
    have hHad := (walshSquare_hadamard 3).reindex e e
    have hr : roundedDimension (7+1)=8 := by decide
    have hH' : ∃ H : Matrix (Fin (roundedDimension (7+1))) (Fin (roundedDimension (7+1))) ℝ,Matrix.IsHadamard H := by
      simpa only [hr] using ⟨_,hHad⟩
    obtain ⟨H,hH⟩ := hH'
    obtain ⟨q,hq,hMass,hMean,hPair,hC,_,_⟩ := cube_law_of_hadamard (d := 7) (by decide) H hH
    refine ⟨q,⟨hq,hMass,hMean,hPair⟩,?_⟩
    simpa only [hr,Nat.cast_ofNat] using hC
  have hCap (q : (Fin 7 → Bool) → ℝ) (hq : cubeProbabilityFeasible q) : collision q≤(1/8 : ℝ) := by
    have hh := (sharp_sign_cube_entropy_bounds (by decide : 2≤7) q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).1
    norm_num [roundedDimension] at hh ⊢
    exact hh
  exact ⟨eightTrapMasks_binary_codes,eightTrapLaw_feasible,eightTrapLaw_support_card,eightTrapLaw_weights,
    eightTrapLaw_collision,hVertex,hLocal,hStrict,hGlobal,hCap⟩

theorem order_eight_character_trap_path_barrier
    (path : ℝ → ((Fin 7 → Bool) → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1))
    (hStart : path 0=eightTrapLaw) (hEnd : collision eightTrapLaw<collision (path 1))
    (hFeasible : ∀ t∈Set.Icc (0 : ℝ) 1,cubeProbabilityFeasible (path t)) :
    ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤(1/16 : ℝ)-1/4352 := by
  classical
  let S := activeSupport eightTrapLaw
  have hPos : 0<S.card := by change 0<(activeSupport eightTrapLaw).card;rw [eightTrapLaw_support_card];norm_num
  obtain ⟨t,ht,hBarrier⟩ := unit_interpolation_path_barrier S hPos eightTrapLaw eightAtomInterpolation
    eightTrapLaw_uniform_on_activeSupport eightTrapLaw_probability.2 eight_atom_interpolation_delta
    (fun x y => eightSeedInterpolation_bounded _ _) path hContinuous hStart hEnd (by
      intro t ht
      have hq := hFeasible t ht
      exact ⟨hq.1,hq.2.1,eight_atom_interpolation_moment (path t) hq⟩)
  refine ⟨t,ht,?_⟩
  norm_num [S,eightTrapLaw_support_card,eightTrapLaw_collision] at hBarrier ⊢
  exact hBarrier



theorem character_trap_global_path_barrier {s : ℕ} (hs : 2≤s) (e : Finset (Fin s)) (he : e.Nonempty)
    (path : ℝ → ((TrapCoordinate s → Bool) → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1))
    (hStart : path 0=trapLaw e) (hEnd : collision (path 1)=1/(2*(2 : ℝ)^s))
    (hFeasible : ∀ t∈Set.Icc (0 : ℝ) 1,observedFeasible (path t)) :
    ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤1/(2 : ℝ)^(2*s)-
      1/(((2 : ℝ)^(2*s))^2*((2 : ℝ)^(2*s)+1)) := by
  have hPow : (4 : ℝ)≤(2 : ℝ)^s := by exact_mod_cast two_pow_ge_four hs
  have hm : (2 : ℝ)^(2*s)=(2 : ℝ)^s*(2 : ℝ)^s := by rw [two_mul,pow_add]
  have hGap : collision (trapLaw e)<collision (path 1) := by
    rw [trapLaw_collision,hEnd,hm]
    exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  exact character_trap_path_barrier e he path hContinuous hStart hGap hFeasible

theorem order_eight_global_path_barrier
    (path : ℝ → ((Fin 7 → Bool) → ℝ)) (hContinuous : ContinuousOn path (Set.Icc 0 1))
    (hStart : path 0=eightTrapLaw) (hEnd : collision (path 1)=(1/8 : ℝ))
    (hFeasible : ∀ t∈Set.Icc (0 : ℝ) 1,cubeProbabilityFeasible (path t)) :
    ∃ t∈Set.Icc (0 : ℝ) 1,collision (path t)≤(1/16 : ℝ)-1/4352 := by
  apply order_eight_character_trap_path_barrier path hContinuous hStart _ hFeasible
  rw [eightTrapLaw_collision,hEnd]
  norm_num


end
end EntropyDesigns
