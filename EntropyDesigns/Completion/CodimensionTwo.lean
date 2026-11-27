/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import EntropyDesigns.Completion.RealExtension
public import Mathlib.Tactic.IntervalCases
@[expose] public section
namespace EntropyDesigns.Completion
open Matrix

/-- A radius-squared-two vector with even integral coordinate sum has sign coordinates. -/
theorem two_flat_of_even_sum (x y : ℝ) (hnorm : x ^ 2 + y ^ 2 = 2)
    (heven : ∃ z : ℤ, x + y = 2 * z) : IsSign x ∧ IsSign y := by
  obtain ⟨z, hz⟩ := heven
  have hsumeq := congrArg (fun u : ℝ => u^2) hz
  have hzsq : (z : ℝ) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x-y)]
  have hzlo : (-1 : ℝ) ≤ z := by nlinarith [sq_nonneg ((z : ℝ)+1)]
  have hzhi : (z : ℝ) ≤ 1 := by nlinarith [sq_nonneg ((z : ℝ)-1)]
  have hlo : (-1 : ℤ) ≤ z := by exact_mod_cast hzlo
  have hhi : z ≤ (1 : ℤ) := by exact_mod_cast hzhi
  interval_cases z
  · norm_num at hz
    have hx : x = -1 := by nlinarith [sq_nonneg (x-y)]
    have hy : y = -1 := by linarith
    exact ⟨Or.inr hx, Or.inr hy⟩
  · norm_num at hz
    have hx : x ^ 2 = 1 := by nlinarith [sq_nonneg (x+y)]
    have hy : y ^ 2 = 1 := by nlinarith
    exact ⟨sq_eq_one_iff.mp hx, sq_eq_one_iff.mp hy⟩
  · norm_num at hz
    have hx : x = 1 := by nlinarith [sq_nonneg (x-y)]
    have hy : y = 1 := by linarith
    exact ⟨Or.inl hx, Or.inl hy⟩

/-- Orthogonal rotation placing a radius-squared-two vector at (1,1). -/
noncomputable def flattenTwo (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(a+b)/2, (b-a)/2; (a-b)/2, (a+b)/2]

theorem flattenTwo_orthogonal (a b : ℝ) (h : a^2+b^2=2) :
    flattenTwo a b * (flattenTwo a b)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flattenTwo, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

theorem flattenTwo_value (a b : ℝ) (h : a^2+b^2=2) :
    (flattenTwo a b).mulVec ![a,b] = ![1,1] := by
  ext i
  fin_cases i <;> simp [flattenTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith


/-- An even number of signs has even integral sum. -/
theorem sign_sum_even {ι : Type*} [Fintype ι]
    (hcard : Even (Fintype.card ι)) (f : ι → ℝ) (hf : ∀ i, IsSign (f i)) :
    ∃ z : ℤ, (∑ i, f i) = 2 * z := by
  classical
  obtain ⟨k, hk⟩ := hcard
  let d : ℕ := ∑ i, if f i = -1 then 1 else 0
  have hd : (d : ℝ) = ∑ i, if f i = -1 then (1 : ℝ) else 0 := by simp [d]
  have hterm : ∀ i, f i = 1 - 2 * (if f i = -1 then (1 : ℝ) else 0) := by
    intro i
    rcases hf i with h | h <;> norm_num [h]
  refine ⟨(k : ℤ) - (d : ℤ), ?_⟩
  calc
    (∑ i, f i) = ∑ i, (1 - 2 * (if f i = -1 then (1 : ℝ) else 0)) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (Fintype.card ι : ℝ) - 2 * d := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hd]
      simp
    _ = 2 * (((k : ℤ) - (d : ℤ) : ℤ) : ℝ) := by
      have hc : (Fintype.card ι : ℝ) = k + k := by exact_mod_cast hk
      push_cast
      linarith


/-- Every even-order real sign frame of codimension two has a sign completion. -/
theorem codimension_two_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (heven : Even (Fintype.card ι))
    (W : Matrix ι (Fin 2 ⊕ ι) ℝ) (hW : IsPartialHadamard W) :
    ∃ L : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℝ,
      Matrix.IsHadamard L ∧ ∀ i j, L (Sum.inr i) j = W i j := by
  classical
  obtain ⟨H, hHr, hHc, hret⟩ := real_frame_extension W hW.2
  let N : ℝ := Fintype.card (Fin 2 ⊕ ι)
  have hNval : N = (Fintype.card ι : ℝ) + 2 := by simp [N]; ring
  have norms (A : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℝ)
      (hAc : Aᵀ * A = N • 1) (hr : ∀ i j, A (Sum.inr i) j = W i j)
      (j : Fin 2 ⊕ ι) : A (Sum.inl 0) j ^ 2 + A (Sum.inl 1) j ^ 2 = 2 := by
    have hs : (∑ i, W i j * W i j) = (Fintype.card ι : ℝ) := by
      have hterm : ∀ i, W i j * W i j = 1 := by
        intro i
        have hi := isSign_sq (hW.1 i j)
        nlinarith
      simp [hterm]
    have hc := congrArg (fun M => M j j) hAc
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, Fintype.sum_sum_type,
      Fin.sum_univ_two] at hc
    simp_rw [hr] at hc
    rw [hs] at hc
    nlinarith [hNval]
  let j₀ : Fin 2 ⊕ ι := Sum.inl 0
  let a := H (Sum.inl 0) j₀
  let b := H (Sum.inl 1) j₀
  have hab : a^2+b^2=2 := norms H hHc hret j₀
  let Q : Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) ℝ :=
    Matrix.fromBlocks (flattenTwo a b) 0 0 1
  have hQ : Q * Qᵀ = 1 := by
    simp [Q, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      flattenTwo_orthogonal a b hab, Matrix.fromBlocks_one]
  have hQc : Qᵀ * Q = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hQ
  let L := Q * H
  have hLr : L * Lᵀ = N • 1 := orthogonal_row_transform Q H N hQ hHr
  have hLc : Lᵀ * L = N • 1 := by
    calc
      Lᵀ * L = Hᵀ * (Qᵀ * Q) * H := by simp [L, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = N • 1 := by rw [hQc]; simpa only [Matrix.mul_one] using hHc
  have hLret : ∀ i j, L (Sum.inr i) j = W i j := by
    intro i j
    simp [L, Q, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
      Matrix.one_apply, hret]
  have htop : L (Sum.inl 0) j₀ = 1 ∧ L (Sum.inl 1) j₀ = 1 := by
    constructor <;>
      simp [L, Q, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
        flattenTwo, Fin.sum_univ_succ, a, b] <;> nlinarith [norms H hHc hret j₀]
  have hNeven : ∃ z : ℤ, N = 2 * z := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨(k : ℤ)+1, ?_⟩
    have hk' : (Fintype.card ι : ℝ) = k + k := by exact_mod_cast hk
    push_cast
    linarith
  have hsign : IsSignMatrix L := by
    intro i j
    cases i with
    | inr i => rw [hLret]; exact hW.1 i j
    | inl i =>
      have hsum : ∃ z : ℤ, (∑ k, W k j₀ * W k j) = 2 * z := by
        apply sign_sum_even heven
        intro k
        rcases hW.1 k j₀ with h0 | h0 <;> rcases hW.1 k j with h1 | h1 <;>
          norm_num [h0,h1,IsSign]
      obtain ⟨z, hz⟩ := hsum
      obtain ⟨q, hq⟩ := hNeven
      have hc := congrArg (fun M => M j₀ j) hLc
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, Fintype.sum_sum_type, Fin.sum_univ_two] at hc
      simp_rw [hLret] at hc
      rw [htop.1, htop.2, one_mul, one_mul, hz] at hc
      have he : ∃ t : ℤ, L (Sum.inl 0) j + L (Sum.inl 1) j = 2 * t := by
        by_cases hj : j₀ = j
        · refine ⟨q-z, ?_⟩
          simp only [hj, ite_true, mul_one] at hc
          push_cast
          linarith
        · refine ⟨-z, ?_⟩
          simp only [hj, ite_false, mul_zero] at hc
          push_cast
          linarith
      have flat := two_flat_of_even_sum _ _ (norms L hLc hLret j) he
      fin_cases i
      · exact flat.1
      · exact flat.2
  exact ⟨L, isHadamard_mathlib ⟨hsign, hLr⟩, hLret⟩

/-- Column-index-independent version, preserving the original rows through an injection. -/
theorem codimension_two_completion_of_card {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι + 2)
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (heven : Even (Fintype.card ι)) :
    ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ),
      Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  classical
  let e : (Fin 2 ⊕ ι) ≃ κ := Fintype.equivOfCardEq (by simp [hcard]; omega)
  let P' : Matrix ι (Fin 2 ⊕ ι) ℝ := P.submatrix id e
  have hP' : IsPartialHadamard P' := by
    constructor
    · intro i j
      exact hP.1 i (e j)
    · change P.submatrix id e * (Pᵀ).submatrix e id =
        (Fintype.card (Fin 2 ⊕ ι) : ℝ) • 1
      rw [Matrix.submatrix_mul_equiv]
      simpa only [Matrix.submatrix_id_id, Fintype.card_congr e] using hP.2
  obtain ⟨H,hH,hret⟩ := codimension_two_completion heven P' hP'
  let rows : ι ↪ κ := ⟨fun i => e (Sum.inr i), e.injective.comp Sum.inr_injective⟩
  refine ⟨Matrix.reindex e e H, rows, hH.reindex e e, ?_⟩
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, rows,
    Function.Embedding.coeFn_mk, e.symm_apply_apply, hret, P', id_eq, e.apply_symm_apply]
    using hret i (e.symm j)

end EntropyDesigns.Completion
