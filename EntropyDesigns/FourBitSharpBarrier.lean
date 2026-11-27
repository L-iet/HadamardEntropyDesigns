/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FourWalshReconstruction
public import EntropyDesigns.FourHalfCoordinateBound
public import EntropyDesigns.FourTranslatedFinite
public import EntropyDesigns.NonuniformTraps
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
set_option Elab.async false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace EntropyDesigns
theorem four_walsh_path_barrier (γ : ℝ → (Fin 5 → ℝ))
    (hc : ContinuousOn γ (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, fourWalshParameterFeasible (γ t))
    (hStart : ∀ i, |γ 0 i|=1/3) (hEnd : ∃ i, |γ 1 i|=1) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ (1+∑ j, γ t j^2)/16 ≤ 3/32 := by
  obtain ⟨i,hi⟩ := hEnd
  have hCont : ContinuousOn (fun t => |γ t i|) (Set.Icc 0 1) :=
    ((continuous_apply i).comp_continuousOn hc).abs
  have hHalf : (1/2:ℝ) ∈ Set.Icc (|γ 0 i|) (|γ 1 i|) := by
    rw [hStart i,hi]
    constructor <;> norm_num
  obtain ⟨t,ht,hEq⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hCont hHalf
  change |γ t i|=1/2 at hEq
  have hBound := four_walsh_half_coordinate_bound (γ t) (hf t ht) i hEq
  have ht0 : t≠0 := by
    intro h; subst t; rw [hStart i] at hEq; norm_num at hEq
  have ht1 : t≠1 := by
    intro h; subst t; rw [hi] at hEq; norm_num at hEq
  exact ⟨t,lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 ht1,by linarith⟩


theorem four_coefficients_feasible (q : (Fin 4 → Bool) → ℝ)
    (hq : cubeProbabilityFeasible q) : fourWalshParameterFeasible (fourWalshCoefficients q) := by
  classical
  intro v hv hp
  let vb : Fin 5 → Bool := fun i => if v i=1 then false else true
  have hV (i : Fin 5) : (bitSign (vb i) : ℝ)=v i := by
    rcases hv i with h|h
    · norm_num [vb,h,bitSign]
    · norm_num [vb,h,bitSign]
  have hProd : (∏ i, bitSign (vb i))=(1:ℤ) := by
    have hReal : (∏ i, (bitSign (vb i) : ℝ))=1 := by simpa only [hV] using hp
    exact_mod_cast hReal
  obtain ⟨x,hx⟩ := four_high_character_certificate.2.2.2.2.2 vb hProd
  have hEq (i : Fin 5) : (fourHighCharacter i x : ℝ)=v i := by
    rw [hx]; exact hV i
  have hRec := four_walsh_reconstruction q hq x
  simp only [hEq,mul_comm] at hRec
  rw [← hRec]
  exact mul_nonneg (hq.1 x) (by norm_num)

theorem four_walsh_collision_identity (q : (Fin 4 → Bool) → ℝ)
    (hq : cubeProbabilityFeasible q) :
    collision q=(1+∑ i : Fin 5, fourWalshCoefficients q i^2)/16 := by
  have h : 16*collision q=1+∑ i : Fin 5, fourWalshCoefficients q i^2 := by
    calc
      16*collision q=∑ x, q x*(16*q x) := by
        unfold collision; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _; ring
      _=∑ x, q x*(1+∑ i : Fin 5, fourWalshCoefficients q i*(fourHighCharacter i x : ℝ)) := by
        apply Finset.sum_congr rfl; intro x _; rw [four_walsh_reconstruction q hq x]
      _=1+∑ i : Fin 5, fourWalshCoefficients q i^2 := by
        simp_rw [mul_add,mul_one,Finset.sum_add_distrib,Finset.mul_sum]
        rw [hq.2.1,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        calc
          _=fourWalshCoefficients q i*(∑ x, q x*(fourHighCharacter i x : ℝ)) := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
          _=fourWalshCoefficients q i^2 := by simp only [fourWalshCoefficients,pow_two]
  linarith

theorem four_cube_path_barrier (γ : ℝ → ((Fin 4 → Bool) → ℝ))
    (hc : ContinuousOn γ (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t))
    (hStart : ∀ i, |fourWalshCoefficients (γ 0) i|=1/3)
    (hEnd : ∃ i, |fourWalshCoefficients (γ 1) i|=1) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ collision (γ t) ≤ 3/32 := by
  have hCoef : Continuous (fun q : ((Fin 4 → Bool) → ℝ) => fourWalshCoefficients q) := by
    unfold fourWalshCoefficients
    fun_prop
  obtain ⟨t,ht0,ht1,hBound⟩ := four_walsh_path_barrier
    (fun t => fourWalshCoefficients (γ t)) (hCoef.comp_continuousOn hc)
    (fun t ht => four_coefficients_feasible (γ t) (hf t ht)) hStart hEnd
  refine ⟨t,ht0,ht1,?_⟩
  rw [four_walsh_collision_identity (γ t) (hf t ⟨ht0.le,ht1.le⟩)]
  exact hBound


noncomputable def fourTranslatedLaw (s : Fin 4 → Bool) (x : Fin 4 → Bool) : ℝ :=
  (fourTranslatedWeights s x : ℝ)
noncomputable def fourUniformLaw (i : Fin 5) (b : Bool) (x : Fin 4 → Bool) : ℝ :=
  (fourUniformWeights i b x : ℝ)

theorem four_translated_feasible (s : Fin 4 → Bool) : cubeProbabilityFeasible (fourTranslatedLaw s) := by
  have h := four_translated_certificate s
  exact rational_trap_feasible_to_cube _ h.1 h.2.1 h.2.2.1

theorem four_uniform_feasible (i : Fin 5) (b : Bool) : cubeProbabilityFeasible (fourUniformLaw i b) := by
  have h := four_uniform_certificate i b
  exact rational_trap_feasible_to_cube _ h.1 h.2.1 h.2.2.1


theorem cube_probability_feasible_segment {d : ℕ} {p q : (Fin d → Bool) → ℝ}
    (hp : cubeProbabilityFeasible p) (hq : cubeProbabilityFeasible q)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    cubeProbabilityFeasible (fun x => (1-t)*p x+t*q x) := by
  rcases hp with ⟨hp, hpm, hpi, hpij⟩
  rcases hq with ⟨hq, hqm, hqi, hqij⟩
  refine ⟨fun x => add_nonneg (mul_nonneg (sub_nonneg.mpr ht') (hp x))
    (mul_nonneg ht (hq x)), ?_, ?_, ?_⟩
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hpm, hqm]
    ring
  · intro i
    simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, hpi, hqi,
      mul_zero, add_zero]
  · intro i j hij
    have h (x : Fin d → Bool) : ((1-t)*p x+t*q x)*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ) =
        (1-t)*(p x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ))+
        t*(q x*(bitSign (x i) : ℝ)*(bitSign (x j) : ℝ)) := by ring
    simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum, hpij i j hij,
      hqij i j hij, mul_zero, add_zero]

theorem collision_segment_formula {α : Type*} [Fintype α] (p q : α → ℝ) (t : ℝ) :
    collision (fun x => (1-t)*p x+t*q x) =
      (1-t)^2*collision p+2*t*(1-t)*(∑ x, p x*q x)+t^2*collision q := by
  unfold collision
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring


theorem four_translated_coefficients (s : Fin 4 → Bool) (i : Fin 5) :
    fourWalshCoefficients (fourTranslatedLaw s) i=(fourHighCharacter i s : ℝ)/3 := by
  unfold fourWalshCoefficients fourTranslatedLaw
  exact_mod_cast (four_translated_certificate s).2.2.2.2.1 i

theorem four_uniform_coefficients (i j : Fin 5) (b : Bool) :
    fourWalshCoefficients (fourUniformLaw i b) j=if j=i then (bitSign b : ℝ) else 0 := by
  unfold fourWalshCoefficients fourUniformLaw
  have h := congrArg (fun r : ℚ => (r:ℝ)) ((four_uniform_certificate i b).2.2.2.2 j)
  by_cases hji : j=i <;> simp [hji] at h ⊢ <;> exact h

theorem four_translated_collision (s : Fin 4 → Bool) :
    collision (fourTranslatedLaw s)=(7/72:ℝ) := by
  have h := congrArg (fun r : ℚ => (r:ℝ)) (four_translated_certificate s).2.2.2.1
  push_cast at h
  norm_num at h
  exact h

theorem four_uniform_collision (i : Fin 5) (b : Bool) :
    collision (fourUniformLaw i b)=(1/8:ℝ) := by
  have h := congrArg (fun r : ℚ => (r:ℝ)) (four_uniform_certificate i b).2.2.2.1
  push_cast at h
  norm_num at h
  exact h

theorem four_bit_all_path_barrier (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (γ : ℝ → ((Fin 4 → Bool) → ℝ))
    (hc : ContinuousOn γ (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t))
    (hStart : γ 0=fourTranslatedLaw s) (hEnd : γ 1=fourUniformLaw i b) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ collision (γ t) ≤ 3/32 ∧
      (1/288:ℝ) ≤ collision (γ 0)-collision (γ t) := by
  have hS (j : Fin 5) : |fourWalshCoefficients (γ 0) j|=1/3 := by
    rw [hStart,four_translated_coefficients]
    rcases (four_translated_certificate s).2.2.2.2.2 j with hj|hj <;>
      rw [hj] <;> norm_num
  have hE : ∃ j, |fourWalshCoefficients (γ 1) j|=1 := by
    refine ⟨i,?_⟩
    rw [hEnd,four_uniform_coefficients]
    cases b <;> norm_num [bitSign]
  obtain ⟨t,ht0,ht1,hB⟩ := four_cube_path_barrier γ hc hf hS hE
  refine ⟨t,ht0,ht1,hB,?_⟩
  rw [hStart,four_translated_collision]
  linarith

theorem four_bit_aligned_escape (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (hb : fourHighCharacter i s=bitSign b) :
    cubeProbabilityFeasible (fourTranslatedLaw s) ∧ cubeProbabilityFeasible (fourUniformLaw i b) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → cubeProbabilityFeasible
      (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)) ∧
    (∀ t : ℝ, collision (fun x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x)=
      3/32+(t-1/4)^2/18) ∧
    (collision (fourUniformLaw i b)-collision (fourTranslatedLaw s)=(1/36:ℝ)) ∧
    (Finset.univ.filter (fun x => fourTranslatedLaw s x≠fourUniformLaw i b x)).card=12 := by
  have hCert := four_aligned_escape_certificate s i b hb
  have hInner : (∑ x, fourTranslatedLaw s x*fourUniformLaw i b x)=(1/12:ℝ) := by
    have h := congrArg (fun r : ℚ => (r:ℝ)) hCert.1
    push_cast at h
    norm_num at h
    exact h
  refine ⟨four_translated_feasible s,four_uniform_feasible i b,
    fun t ht ht' => cube_probability_feasible_segment
      (four_translated_feasible s) (four_uniform_feasible i b) ht ht',?_,?_,?_⟩
  · intro t
    rw [collision_segment_formula,four_translated_collision,four_uniform_collision,hInner]
    ring
  · rw [four_uniform_collision,four_translated_collision]; norm_num
  · have hNe (x : Fin 4 → Bool) :
        (fourTranslatedLaw s x≠fourUniformLaw i b x) ↔
        (fourTranslatedWeights s x≠fourUniformWeights i b x) := by
      unfold fourTranslatedLaw fourUniformLaw
      exact not_congr Rat.cast_inj
    simp_rw [hNe]
    exact hCert.2


theorem four_bit_barrier_sharpness (s : Fin 4 → Bool) (i : Fin 5) :
    ∃ (b : Bool) (γ : ℝ → ((Fin 4 → Bool) → ℝ)),
      fourHighCharacter i s=bitSign b ∧
      Continuous γ ∧ γ 0=fourTranslatedLaw s ∧ γ 1=fourUniformLaw i b ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t)) ∧
      (∀ t : ℝ, (3/32:ℝ) ≤ collision (γ t)) ∧
      collision (γ (1/4))=(3/32:ℝ) ∧
      collision (γ 0)-collision (γ (1/4))=(1/288:ℝ) := by
  have hB : ∃ b : Bool, fourHighCharacter i s=bitSign b := by
    rcases (four_translated_certificate s).2.2.2.2.2 i with h|h
    · exact ⟨false,by simpa only [bitSign, Bool.false_eq_true,ite_false] using h⟩
    · exact ⟨true,by simpa only [bitSign,ite_true] using h⟩
  obtain ⟨b,hb⟩ := hB
  have hPath := four_bit_aligned_escape s i b hb
  let γ : ℝ → ((Fin 4 → Bool) → ℝ) :=
    fun t x => (1-t)*fourTranslatedLaw s x+t*fourUniformLaw i b x
  have h0 : γ 0=fourTranslatedLaw s := by ext x; simp [γ]
  have h1 : γ 1=fourUniformLaw i b := by ext x; simp [γ]
  have hC (t : ℝ) : collision (γ t)=3/32+(t-1/4)^2/18 := hPath.2.2.2.1 t
  refine ⟨b,γ,hb,?_,h0,h1,fun t ht => hPath.2.2.1 t ht.1 ht.2,?_,?_,?_⟩
  · unfold γ; fun_prop
  · intro t; rw [hC]; nlinarith [sq_nonneg (t-1/4)]
  · rw [hC]; norm_num
  · rw [h0,four_translated_collision,hC]; norm_num

theorem four_bit_no_monotone_escape (s : Fin 4 → Bool) (i : Fin 5) (b : Bool)
    (γ : ℝ → ((Fin 4 → Bool) → ℝ))
    (hc : ContinuousOn γ (Set.Icc 0 1))
    (hf : ∀ t ∈ Set.Icc (0:ℝ) 1, cubeProbabilityFeasible (γ t))
    (hStart : γ 0=fourTranslatedLaw s) (hEnd : γ 1=fourUniformLaw i b) :
    ¬MonotoneOn (fun t => collision (γ t)) (Set.Icc 0 1) := by
  obtain ⟨t,ht0,ht1,hBound,hLoss⟩ := four_bit_all_path_barrier s i b γ hc hf hStart hEnd
  intro hm
  have hLe := hm (by constructor <;> norm_num : (0:ℝ) ∈ Set.Icc 0 1)
    ⟨ht0.le,ht1.le⟩ ht0.le
  linarith

end EntropyDesigns
