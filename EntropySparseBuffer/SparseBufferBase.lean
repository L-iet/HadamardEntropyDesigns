/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyDesigns.FiniteFourier
public import EntropyDesigns.CorrectionObstruction
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
@[expose] public section
set_option maxHeartbeats 1000000
namespace EntropyDesigns

theorem off_support_positive_mass {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (f : α → ℝ) (L B S : ℝ)
    (hL : 0≤L) (hB : 0≤B) (hmean : ∑ x,f x=0)
    (hsquare : ∑ x,f x^2=(Fintype.card α : ℝ)*S)
    (hbound : ∀ x,|f x|≤L) (hoff : ∀ x,x∉T → f x≤B) :
    (Fintype.card α : ℝ)*S≤2*(T.card : ℝ)*L^2+2*(Fintype.card α : ℝ)*B*L := by
  have hpoint (x : α) : |f x|=2*max (f x) 0-f x := by
    by_cases h : 0≤f x
    · rw [abs_of_nonneg h,max_eq_left h]; ring
    · have hn : f x≤0 := by linarith
      rw [abs_of_nonpos hn,max_eq_right hn]; ring
  have habs : (∑ x,|f x|)=2*∑ x,max (f x) 0 := by
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,hmean]
    ring
  have hmax (x : α) : max (f x) 0≤(if x∈T then L else 0)+B := by
    by_cases hx : x∈T
    · rw [if_pos hx]
      exact (max_le (le_trans (le_abs_self _) (hbound x)) hL).trans (by linarith)
    · rw [if_neg hx,zero_add]
      exact max_le (hoff x hx) hB
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hmax x)
  have htotal : (∑ x,max (f x) 0)≤(T.card : ℝ)*L+(Fintype.card α : ℝ)*B := by
    simpa [Finset.sum_add_distrib,Finset.sum_ite] using hsum
  have hsq (x : α) : f x^2≤L*|f x| := by
    have he := sq_abs (f x)
    nlinarith [mul_nonneg (sub_nonneg.mpr (hbound x)) (abs_nonneg (f x))]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hsq x)
  rw [← Finset.mul_sum,hsquare,habs] at h
  nlinarith [mul_le_mul_of_nonneg_left htotal hL]

theorem off_support_buffer_lower {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (f : α → ℝ) (K σ B : ℝ)
    (hM : 0<(Fintype.card α : ℝ)) (hK : 0<K) (hσ : 0<σ) (hB : 0≤B)
    (hsize : 4*(T.card : ℝ)*K≤Fintype.card α)
    (hmean : ∑ x,f x=0) (hsquare : ∑ x,f x^2=(Fintype.card α : ℝ)*σ^2)
    (hbound : ∀ x,|f x|≤Real.sqrt K*σ) (hoff : ∀ x,x∉T → f x≤B) :
    σ/(4*Real.sqrt K)≤B := by
  have hr : 0<Real.sqrt K := Real.sqrt_pos.mpr hK
  have hs := off_support_positive_mass T f (Real.sqrt K*σ) B (σ^2)
    (by positivity) hB hmean hsquare hbound hoff
  have he := Real.sq_sqrt hK.le
  rw [mul_pow,he] at hs
  have hsize' := mul_le_mul_of_nonneg_right hsize (sq_nonneg σ)
  have hprod : 0≤(Fintype.card α : ℝ)*σ := by positivity
  have hclaim : σ≤4*B*Real.sqrt K := by
    by_contra hn
    have hdiff : 0<σ-4*B*Real.sqrt K := by linarith
    have hh : 0<(Fintype.card α : ℝ)*σ*(σ-4*B*Real.sqrt K) := by positivity
    nlinarith
  apply (div_le_iff₀ (by positivity : 0<4*Real.sqrt K)).mpr
  nlinarith

theorem lowIndex_card (d : ℕ) : Fintype.card (LowIndex d)=d+d.choose 2 := by
  classical
  let A := (Finset.univ : Finset (Fin d)).powersetCard 1
  let B := (Finset.univ : Finset (Fin d)).powersetCard 2
  have hiff (S : Finset (Fin d)) :
      (S.Nonempty ∧ S.card≤2) ↔ S∈A∪B := by
    simp only [Finset.mem_union,A,B,Finset.mem_powersetCard,Finset.subset_univ,true_and]
    constructor
    · rintro ⟨hn,hc⟩
      have hp := Finset.card_pos.mpr hn
      omega
    · intro hc
      exact ⟨Finset.card_pos.mp (by omega),by omega⟩
  let e : LowIndex d ≃ ↥(A∪B) := Equiv.subtypeEquivRight hiff
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro S hA hB
    have h₁ := (Finset.mem_powersetCard.mp hA).2
    have h₂ := (Finset.mem_powersetCard.mp hB).2
    omega
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_union_of_disjoint hdis]
  simp [A,B]

theorem lowIndex_card_twice (d : ℕ) : 2*Fintype.card (LowIndex d)=d*(d+1) := by
  have h := Nat.add_one_mul_choose_eq d 1
  rw [Nat.choose_succ_succ] at h
  simp only [Nat.choose_one_right] at h
  rw [lowIndex_card]
  nlinarith

theorem lowPolynomial_cauchy {d : ℕ} (w : (Fin d → Bool) → ℝ)
    (x : Fin d → Bool) :
    |lowPolynomial w x|≤Real.sqrt (Fintype.card (LowIndex d)) *
      Real.sqrt (∑ i : LowIndex d,fourierCoefficient w lowCharacter i^2) := by
  classical
  let S := ∑ i : LowIndex d,fourierCoefficient w lowCharacter i^2
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (LowIndex d))
    (fourierCoefficient w lowCharacter) (fun i => lowCharacter i x)
  have hchar (i : LowIndex d) : lowCharacter i x^2=1 := by
    have hh := lowCharacter_abs i x
    nlinarith [sq_abs (lowCharacter i x)]
  simp only [hchar,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hc
  change lowPolynomial w x^2≤S*Fintype.card (LowIndex d) at hc
  have hk := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card (LowIndex d)) : (0:ℝ)≤_)
  have hs := Real.sq_sqrt hS
  have hroot : (Real.sqrt (Fintype.card (LowIndex d))*Real.sqrt S)^2=
      (Fintype.card (LowIndex d) : ℝ)*S := by rw [mul_pow,hk,hs]
  have hnonneg : 0≤Real.sqrt (Fintype.card (LowIndex d))*Real.sqrt S := by positivity
  have ha := abs_nonneg (lowPolynomial w x)
  have habs := sq_abs (lowPolynomial w x)
  change |lowPolynomial w x|≤Real.sqrt (Fintype.card (LowIndex d))*Real.sqrt S
  nlinarith

theorem binary_cube_polynomial_bound {d : ℕ} (hd : 16≤d) :
    2*(d+4)*d*(d+1)≤2^d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hd
  clear hd
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hx : 16≤16+k := by omega
    have hpoly : (16+k+5)*(16+k+2)≤2*(16+k+4)*(16+k) := by nlinarith
    have hs := Nat.mul_le_mul_left (2*(16+k+1)) hpoly
    have hi := Nat.mul_le_mul_left 2 ih
    rw [show 16+(k+1)=(16+k)+1 by omega,pow_succ]
    nlinarith

theorem cube_fourfold_lowIndex_target {d : ℕ} (hd : 16≤d) :
    4*(d+4)*Fintype.card (LowIndex d)≤2^d := by
  have h := lowIndex_card_twice d
  have hh := binary_cube_polynomial_bound hd
  nlinarith [Nat.mul_le_mul_left (2*(d+4)) h.le]

theorem fractional_buffer_drop {b : ℝ} (hb : 0≤b) (hb1 : b≤1) :
    b/2≤1-1/(1+b)^2 := by
  have hden : 1+b≠0 := by linarith
  have hid : (1-1/(1+b)^2)-b/2=b*(3-b^2)/(2*(1+b)^2) := by
    field_simp
    ring
  have hsq : b^2≤1 := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hb1)]
  have hh : 0≤b*(3-b^2)/(2*(1+b)^2) := div_nonneg (mul_nonneg hb (by linarith)) (by positivity)
  rw [← hid] at hh
  linarith

theorem feasible_buffer_collision_gap {N M B b S Q : ℝ}
    (hN : 0<N) (hM : 2*N≤M) (hb : 0<b) (hb1 : b≤1) (hB : b≤B)
    (hS : 0≤S)
    (hQ : Q=1/M+(1/N-(1+S)/M)/(1+B)^2) :
    b/(4*N)≤1/N-Q := by
  have hMp : 0<M := by linarith
  have hBp : 0<B := hb.trans_le hB
  have hden : 0<(1+B)^2 := by positivity
  have hgap := large_cube_reciprocal_gap hN hM
  have hrecip := one_div_le_one_div_of_le (by positivity : 0<(1+b)^2)
    (show (1+b)^2≤(1+B)^2 by nlinarith)
  have hdrop : b/2≤1-1/(1+B)^2 := by linarith [fractional_buffer_drop hb.le hb1]
  have hg0 : 0≤1/N-1/M := (by positivity : 0≤1/(2*N)).trans hgap
  have hprod := mul_le_mul hgap hdrop (by positivity : 0≤b/2) hg0
  have hid : (1/N-Q)-(1/N-1/M)*(1-1/(1+B)^2)=S/(M*(1+B)^2) := by
    rw [hQ]
    field_simp
    ring
  have hnonneg : 0≤S/(M*(1+B)^2) := div_nonneg hS (by positivity)
  have hsmall : (1/(2*N))*(b/2)=b/(4*N) := by field_simp; ring
  rw [hsmall] at hprod
  linarith

theorem uniform_low_energy_lower {d N : ℕ} (G : Finset (Fin d → Bool))
    (hcard : G.card=N) (hN : 0<N) (heven : Even N)
    (hnonzero : ∃ i : LowIndex d,fourierCoefficient (uniformOn G N) lowCharacter i≠0) :
    2/(N : ℝ)≤Real.sqrt (∑ i : LowIndex d,fourierCoefficient (uniformOn G N) lowCharacter i^2) := by
  classical
  obtain ⟨i,hi⟩ := hnonzero
  have hl := uniform_cube_coefficient_lower G hcard hN heven i hi
  have hsingle : fourierCoefficient (uniformOn G N) lowCharacter i^2≤
      ∑ j : LowIndex d,fourierCoefficient (uniformOn G N) lowCharacter j^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hn : 0<(N : ℝ) := by exact_mod_cast hN
  have hpos : 0<2/(N : ℝ) := by positivity
  have hsum : 0≤∑ j : LowIndex d,fourierCoefficient (uniformOn G N) lowCharacter j^2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hs := Real.sq_sqrt hsum
  have ha := abs_nonneg (fourierCoefficient (uniformOn G N) lowCharacter i)
  have he := sq_abs (fourierCoefficient (uniformOn G N) lowCharacter i)
  have hr := Real.sqrt_nonneg (∑ j : LowIndex d,fourierCoefficient (uniformOn G N) lowCharacter j^2)
  nlinarith

theorem feasible_correction_off_support {α : Type*} [Fintype α] [DecidableEq α]
    (G : Finset α) (N : ℕ) (f : α → ℝ) (M B : ℝ)
    (hM : 0<M) (hB : 0≤B)
    (hfeasible : ∀ x,0≤affineCorrection (uniformOn G N) f M B x) :
    ∀ x,x∉G → f x≤B := by
  intro x hx
  have hden : 1+B≠0 := by linarith
  have hid : affineCorrection (uniformOn G N) f M B x*(M*(1+B))=B-f x := by
    unfold affineCorrection uniformOn
    rw [if_neg hx]
    field_simp
    ring
  have hprod := mul_nonneg (hfeasible x) (show 0≤M*(1+B) by positivity)
  rw [hid] at hprod
  linarith

theorem minimal_feasible_uniform_buffer_lower {d : ℕ} (hd : 16≤d)
    (G : Finset (Fin d → Bool)) (hcard : G.card=d+4) (heven : Even (d+4))
    (hnonzero : ∃ i : LowIndex d,fourierCoefficient (uniformOn G (d+4)) lowCharacter i≠0)
    (B : ℝ) (hB : 0≤B)
    (hfeasible : ∀ x,0≤affineCorrection (uniformOn G (d+4))
      (lowPolynomial (uniformOn G (d+4))) ((2:ℝ)^d) B x) :
    1/(2*((d:ℝ)+4)*Real.sqrt (Fintype.card (LowIndex d)))≤B := by
  classical
  let w := uniformOn G (d+4)
  let S := ∑ i : LowIndex d,fourierCoefficient w lowCharacter i^2
  let σ := Real.sqrt S
  let K : ℝ := Fintype.card (LowIndex d)
  have hS : 0≤S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hσlow : 2/((d:ℝ)+4)≤σ := by
    have hh := uniform_low_energy_lower G hcard (by omega) heven hnonzero
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hh
  have hσ : 0<σ := lt_of_lt_of_le (by positivity) hσlow
  have hK : 0<K := by
    have hc : 2*K=(d:ℝ)*((d:ℝ)+1) := by dsimp only [K]; exact_mod_cast lowIndex_card_twice d
    have hdR : (16:ℝ)≤d := by exact_mod_cast hd
    nlinarith
  have hM : 0<(Fintype.card (Fin d → Bool) : ℝ) := by simp
  have hsize : 4*(G.card : ℝ)*K≤Fintype.card (Fin d → Bool) := by
    have hh := cube_fourfold_lowIndex_target hd
    rw [← hcard] at hh
    dsimp only [K]
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact_mod_cast hh
  have hmean : (∑ x,lowPolynomial w x)=0 := lowPolynomial_sum_zero w
  have hsquare : (∑ x,lowPolynomial w x^2)=(Fintype.card (Fin d → Bool):ℝ)*σ^2 := by
    have hh := fourierPolynomial_square (fourierCoefficient w lowCharacter)
      lowCharacter ((2:ℝ)^d) lowCharacter_orthogonality
    change (∑ x,lowPolynomial w x^2)=(2:ℝ)^d*S at hh
    dsimp only [σ]
    rw [Real.sq_sqrt hS]
    simpa using hh
  have hbound : ∀ x,|lowPolynomial w x|≤Real.sqrt K*σ := lowPolynomial_cauchy w
  have hoff := feasible_correction_off_support G (d+4) (lowPolynomial w) ((2:ℝ)^d) B
    (by positivity) hB hfeasible
  have hl := off_support_buffer_lower G (lowPolynomial w) K σ B
    hM hK hσ hB hsize hmean hsquare hbound hoff
  have hr : 0<Real.sqrt K := Real.sqrt_pos.mpr hK
  have hdiv := div_le_div_of_nonneg_right hσlow (by positivity : 0≤4*Real.sqrt K)
  have hid : (2/((d:ℝ)+4))/(4*Real.sqrt K)=1/(2*((d:ℝ)+4)*Real.sqrt K) := by
    field_simp
    ring
  rw [hid] at hdiv
  exact hdiv.trans hl

end EntropyDesigns
