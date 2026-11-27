/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Modified imports for bounded compilation; mathematical statements and proof bodies are unchanged. -/
module
public import EntropyDesigns.SignArithmetic
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
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Trace
@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
open scoped Matrix.Norms.Frobenius
namespace EntropyDesigns

def signRowParity {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℤ := ∏ j, H i j

def signGramError {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℤ :=
  (∑ k, H i k*H j k)-(if i=j then (n:ℤ) else 0)

theorem sign_gram_parity_pointwise (n : ℕ) (hn : n%4=2)
    (H : Matrix (Fin n) (Fin n) ℤ) (hH : ∀ i j, H i j=1 ∨ H i j= -1)
    (i j : Fin n) :
    2+2*signRowParity H i*signRowParity H j-(if i=j then 4 else 0)≤signGramError H i j^2 := by
  by_cases hij : i=j
  · subst j
    have hp := prod_sign Finset.univ (H i) (fun j _ => hH i j)
    have hDot : (∑ k, H i k*H i k)=(n:ℤ) := by
      have he (k : Fin n) : H i k*H i k=1 := by rcases hH i k with h|h <;> simp [h]
      simp [he]
    rcases hp with hp|hp <;> simp [signRowParity,signGramError,hDot,hp]
  · have hSign (k : Fin n) : H i k*H j k=1 ∨ H i k*H j k= -1 := by
      rcases hH i k with h|h <;> rcases hH j k with h'|h' <;> simp [h,h']
    have h := residue_two_sign_square_lower Finset.univ (fun k => H i k*H j k)
      (fun k _ => hSign k) (by simpa using hn)
    simpa [signGramError,hij,Finset.prod_mul_distrib,signRowParity,mul_assoc] using h

theorem sign_gram_error_parity_floor (n : ℕ) (hn : n%4=2)
    (H : Matrix (Fin n) (Fin n) ℤ) (hH : ∀ i j, H i j=1 ∨ H i j= -1) :
    2*(n:ℤ)*((n:ℤ)-2)≤∑ i, ∑ j, signGramError H i j^2 := by
  have hAll := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ => sign_gram_parity_pointwise n hn H hH i j))
  have hConst : (∑ i : Fin n, ∑ j : Fin n, (2:ℤ))=2*(n:ℤ)*(n:ℤ) := by simp; ring
  have hCross : (∑ i, ∑ j, 2*signRowParity H i*signRowParity H j)=
      2*(∑ i, signRowParity H i)^2 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul,← Finset.mul_sum]
    ring
  have hDiag : (∑ i : Fin n, ∑ j : Fin n, (if i=j then (4:ℤ) else 0))=4*(n:ℤ) := by simp [mul_comm]
  have hSum : (∑ i : Fin n, ∑ j : Fin n,
      (2+2*signRowParity H i*signRowParity H j-(if i=j then 4 else 0)))=
      2*(n:ℤ)*(n:ℤ)+2*(∑ i, signRowParity H i)^2-4*(n:ℤ) := by
    simp_rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [hConst,hCross,hDiag]
  rw [hSum] at hAll
  nlinarith [sq_nonneg (∑ i, signRowParity H i)]


theorem real_frobenius_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : ‖M‖^2=∑ i, ∑ j, M i j^2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (M i j)))

theorem real_frobenius_sq_trace {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : ‖M‖^2=Matrix.trace (M*M.transpose) := by
  rw [real_frobenius_norm_sq]
  simp [Matrix.trace,Matrix.mul_apply,Matrix.transpose_apply,pow_two]

theorem orthogonal_left_frobenius_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U M : Matrix ι ι ℝ) (hU : U.transpose*U=1) : ‖U*M‖=‖M‖ := by
  have hs : ‖U*M‖^2=‖M‖^2 := by
    rw [real_frobenius_sq_trace,real_frobenius_sq_trace,Matrix.transpose_mul]
    calc
      _=Matrix.trace (U*(M*M.transpose)*U.transpose) := by congr 1; noncomm_ring
      _=Matrix.trace (U.transpose*U*(M*M.transpose)) := Matrix.trace_mul_cycle _ _ _
      _=Matrix.trace (M*M.transpose) := by rw [hU,Matrix.one_mul]
  nlinarith [norm_nonneg (U*M),norm_nonneg M]

theorem orthogonal_gram_distance_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U E : Matrix ι ι ℝ) (hU : U*U.transpose=1) (hUt : U.transpose*U=1) :
    ‖(U+E)*(U+E).transpose-1‖≤2*‖E‖+‖E‖^2 := by
  have hEq : (U+E)*(U+E).transpose-1=U*E.transpose+E*U.transpose+E*E.transpose := by
    rw [Matrix.transpose_add]
    calc
      _=(U*U.transpose-1)+(U*E.transpose+E*U.transpose+E*E.transpose) := by noncomm_ring
      _=_ := by rw [hU,sub_self,zero_add]
  have hA : ‖U*E.transpose‖=‖E‖ := by
    rw [orthogonal_left_frobenius_invariant U E.transpose hUt,Matrix.frobenius_norm_transpose]
  have hB : ‖E*U.transpose‖=‖E‖ := by
    rw [← Matrix.frobenius_norm_transpose (E*U.transpose),Matrix.transpose_mul,Matrix.transpose_transpose,hA]
  have hC : ‖E*E.transpose‖≤‖E‖^2 := by
    simpa only [Matrix.frobenius_norm_transpose,pow_two] using Matrix.frobenius_norm_mul E E.transpose
  rw [hEq]
  have h := norm_add_le (U*E.transpose+E*U.transpose) (E*E.transpose)
  have h2 := norm_add_le (U*E.transpose) (E*U.transpose)
  rw [hA,hB] at h2
  linarith


noncomputable def parityGapExact (N : ℝ) : ℝ :=
  (Real.sqrt (1+Real.sqrt (2*(N-2)/N))-1)^2/N

noncomputable def parityGapSimple (N : ℝ) : ℝ := 2*(N-2)/(9*N^2)

theorem parity_gap_exact_dominates_simple (N : ℝ) (hN : 2≤N) :
    parityGapSimple N≤parityGapExact N := by
  have hNpos : 0<N := by linarith
  have hRatio : 0≤2*(N-2)/N := div_nonneg (by linarith) hNpos.le
  have hRatioUpper : 2*(N-2)/N≤2 := (div_le_iff₀ hNpos).mpr (by linarith)
  let L := Real.sqrt (2*(N-2)/N)
  let a := Real.sqrt (1+L)
  have hL0 : 0≤L := Real.sqrt_nonneg _
  have hL2 : L^2=2*(N-2)/N := Real.sq_sqrt hRatio
  have hLBound : L≤2 := by nlinarith
  have ha0 : 0≤a := Real.sqrt_nonneg _
  have ha2 : a^2=1+L := Real.sq_sqrt (by positivity)
  have haBound : a≤2 := by nlinarith
  have hIdentity : (a-1)^2*(a+1)^2=L^2 := by
    calc
      _=(a^2-1)^2 := by ring
      _=L^2 := by rw [ha2]; ring
  have hDenBound : (a+1)^2≤9 := by nlinarith
  have hNine : L^2≤9*(a-1)^2 := by
    rw [← hIdentity]
    nlinarith [mul_le_mul_of_nonneg_left hDenBound (sq_nonneg (a-1))]
  have hR : 2*(N-2)≤9*(a-1)^2*N := (div_le_iff₀ hNpos).mp (by rw [← hL2]; exact hNine)
  change 2*(N-2)/(9*N^2)≤(a-1)^2/N
  apply (div_le_div_iff₀ (by positivity : 0<9*N^2) hNpos).mpr
  have hMult := mul_le_mul_of_nonneg_right hR hNpos.le
  nlinarith

theorem parity_gap_from_rounding_distance (N d v : ℝ) (hN : 0<N) (hd : 0≤d)
    (hLower : Real.sqrt (2*(N-2)/N)≤2*d+d^2) (hUpper : d^2≤N*v) :
    parityGapExact N≤v := by
  let L := Real.sqrt (2*(N-2)/N)
  let a := Real.sqrt (1+L)
  have hL : 0≤L := Real.sqrt_nonneg _
  have ha : 0≤a := Real.sqrt_nonneg _
  have ha2 : a^2=1+L := Real.sq_sqrt (by positivity)
  have ha1 : 1≤a := by nlinarith
  have hdA : a-1≤d := by nlinarith
  have hSq : (a-1)^2≤d^2 := by nlinarith
  apply (div_le_iff₀ hN).mpr
  simpa only [mul_comm] using hSq.trans hUpper


noncomputable def parityRoundSign (x : ℝ) : ℤ := if x<0 then -1 else 1

theorem parity_round_sign_is_sign (x : ℝ) : parityRoundSign x=1 ∨ parityRoundSign x= -1 := by
  unfold parityRoundSign
  split_ifs <;> simp

theorem parity_rounding_square (x a : ℝ) :
    (a*(parityRoundSign x : ℝ)-x)^2=(|x|-a)^2 := by
  by_cases hx : x<0
  · simp [parityRoundSign,hx,abs_of_neg hx] <;> ring
  · simp [parityRoundSign,hx,abs_of_nonneg (le_of_not_gt hx)] <;> ring

theorem matching_square_deviation_bound (x a : ℝ) (ha : 0≤a) :
    (|x|-a)^2*a^2≤(x^2-a^2)^2 := by
  have hFactor : a^2≤(|x|+a)^2 := by nlinarith [abs_nonneg x]
  calc
    _≤(|x|-a)^2*(|x|+a)^2 := mul_le_mul_of_nonneg_left hFactor (sq_nonneg (|x|-a))
    _=(x^2-a^2)^2 := by rw [← sq_abs x]; ring

theorem orthogonal_quartic_variance_identity (n : ℕ) (hn : 0<n)
    (U : Matrix (Fin n) (Fin n) ℝ) (hRows : ∀ i, ∑ j, U i j^2=1) :
    (∑ i, ∑ j, (U i j^2-1/(n:ℝ))^2)=(∑ i, ∑ j, U i j^4)-1 := by
  have hN : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hMass : (∑ i, ∑ j, U i j^2)=(n:ℝ) := by simp_rw [hRows]; simp
  have he (i j : Fin n) : (U i j^2-1/(n:ℝ))^2=
      U i j^4-(2/(n:ℝ))*U i j^2+(1/(n:ℝ))^2 := by ring
  simp_rw [he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hMass]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

theorem normalized_sign_rounding_distance (n : ℕ) (hn : 0<n)
    (U : Matrix (Fin n) (Fin n) ℝ) :
    let H : Matrix (Fin n) (Fin n) ℤ := fun i j => parityRoundSign (U i j)
    let C := (1/Real.sqrt (n:ℝ)) • H.map (Int.castRingHom ℝ)
    ‖C-U‖^2≤(n:ℝ)*(∑ i, ∑ j, (U i j^2-1/(n:ℝ))^2) := by
  have hN : (0:ℝ)<n := by exact_mod_cast hn
  have hRoot : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hN
  have ha : (1/Real.sqrt (n:ℝ))^2=1/(n:ℝ) := by
    rw [div_pow,one_pow,Real.sq_sqrt hN.le]
  dsimp only
  rw [real_frobenius_norm_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  change ((1/Real.sqrt (n:ℝ))*(parityRoundSign (U i j) : ℝ)-U i j)^2≤_
  rw [parity_rounding_square]
  have h := matching_square_deviation_bound (U i j) (1/Real.sqrt (n:ℝ)) (by positivity)
  rw [ha] at h
  have hm := mul_le_mul_of_nonneg_right h hN.le
  calc
    _=((|U i j|-1/Real.sqrt (n:ℝ))^2*(1/(n:ℝ)))*(n:ℝ) := by field_simp
    _≤(U i j^2-1/(n:ℝ))^2*(n:ℝ) := hm
    _=(n:ℝ)*(U i j^2-1/(n:ℝ))^2 := by ring


theorem real_sign_gram_error_floor (n : ℕ) (hn : n%4=2)
    (H : Matrix (Fin n) (Fin n) ℤ) (hH : ∀ i j, H i j=1 ∨ H i j= -1) :
    2*(n:ℝ)*((n:ℝ)-2)≤
      ‖H.map (Int.castRingHom ℝ)*(H.map (Int.castRingHom ℝ)).transpose-
        (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)‖^2 := by
  have h := sign_gram_error_parity_floor n hn H hH
  simp only [signGramError] at h
  rw [real_frobenius_norm_sq]
  simp only [Matrix.sub_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.map_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_one,mul_zero]
  change 2*(n:ℝ)*((n:ℝ)-2)≤∑ i, ∑ j,
    ((∑ k, (H i k : ℝ)*(H j k : ℝ))-(if i=j then (n:ℝ) else 0))^2
  exact_mod_cast h

theorem normalized_sign_gram_error_lower (n : ℕ) (hn : n%4=2)
    (H : Matrix (Fin n) (Fin n) ℤ) (hH : ∀ i j, H i j=1 ∨ H i j= -1) :
    let C := (1/Real.sqrt (n:ℝ)) • H.map (Int.castRingHom ℝ)
    Real.sqrt (2*((n:ℝ)-2)/(n:ℝ))≤‖C*C.transpose-1‖ := by
  have hnPos : 0<n := by omega
  have hN : (0:ℝ)<n := by exact_mod_cast hnPos
  have hNne : (n:ℝ)≠0 := hN.ne'
  have ha : (1/Real.sqrt (n:ℝ))^2=1/(n:ℝ) := by
    rw [div_pow,one_pow,Real.sq_sqrt hN.le]
  let M := H.map (Int.castRingHom ℝ)
  let C := (1/Real.sqrt (n:ℝ)) • M
  have hEq : C*C.transpose-1=(1/(n:ℝ)) • (M*M.transpose-(n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    dsimp [C]
    simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← pow_two,ha]
    rw [smul_sub,smul_smul,one_div_mul_cancel hNne,one_smul]
  have hFloor := real_sign_gram_error_floor n hn H hH
  have hm := mul_le_mul_of_nonneg_left hFloor (sq_nonneg (1/(n:ℝ)))
  have hCoeff : (1/(n:ℝ))^2*(2*(n:ℝ)*((n:ℝ)-2))=2*((n:ℝ)-2)/(n:ℝ) := by
    field_simp <;> ring
  rw [hCoeff] at hm
  have hSq : 2*((n:ℝ)-2)/(n:ℝ)≤‖C*C.transpose-1‖^2 := by
    rw [hEq,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hN),mul_pow]
    exact hm
  exact (Real.sqrt_le_iff).mpr ⟨norm_nonneg _,hSq⟩

theorem elementary_orthogonal_parity_gap (n : ℕ) (hn : n%4=2)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : U*U.transpose=1) (hUt : U.transpose*U=1) :
    parityGapExact (n:ℝ)≤(∑ i, ∑ j, U i j^4)-1 ∧
    parityGapSimple (n:ℝ)≤parityGapExact (n:ℝ) ∧
    ‖Matrix.of (fun i j : Fin n => U i j^2-1/(n:ℝ))‖^2=
      (∑ i, ∑ j, U i j^4)-1 := by
  have hn2 : 2≤n := by omega
  have hnPos : 0<n := by omega
  have hN : (0:ℝ)<n := by exact_mod_cast hnPos
  have hRows (i : Fin n) : ∑ j, U i j^2=1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) hU
    simpa [Matrix.mul_apply,Matrix.transpose_apply,pow_two] using h
  have hVariance := orthogonal_quartic_variance_identity n hnPos U hRows
  let H : Matrix (Fin n) (Fin n) ℤ := fun i j => parityRoundSign (U i j)
  let C := (1/Real.sqrt (n:ℝ)) • H.map (Int.castRingHom ℝ)
  have hH (i j : Fin n) : H i j=1 ∨ H i j= -1 := parity_round_sign_is_sign _
  have hLower := normalized_sign_gram_error_lower n hn H hH
  have hUpper := orthogonal_gram_distance_bound U (C-U) hU hUt
  have hC : U+(C-U)=C := by abel
  rw [hC] at hUpper
  have hDist : ‖C-U‖^2≤(n:ℝ)*((∑ i, ∑ j, U i j^4)-1) := by
    have h := normalized_sign_rounding_distance n hnPos U
    rw [hVariance] at h
    exact h
  refine ⟨parity_gap_from_rounding_distance (n:ℝ) ‖C-U‖ _ hN (norm_nonneg _) (hLower.trans hUpper) hDist,
    parity_gap_exact_dominates_simple (n:ℝ) (by exact_mod_cast hn2),?_⟩
  calc
    _=(∑ i, ∑ j, (U i j^2-1/(n:ℝ))^2) := real_frobenius_norm_sq _
    _=_ := hVariance

end EntropyDesigns
