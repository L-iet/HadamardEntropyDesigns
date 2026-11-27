/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import EntropyDesigns.Completion.TetrahedralCompletion
public import EntropyDesigns.Completion.CodimensionOne
public import EntropyDesigns.Completion.CodimensionTwo
@[expose] public section
namespace EntropyDesigns.Completion
open Matrix

/-- The number of negative signs controls both the sum and the product. -/
theorem sign_sum_product_data {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, IsSign (f i)) :
    ∃ d : ℕ, (∑ i, f i) = (Fintype.card ι : ℝ)-2*d ∧ (∏ i, f i)=(-1 : ℝ)^d := by
  classical
  let d := (Finset.univ.filter (fun i => f i = -1)).card
  have ht (i : ι) : f i = (if f i = -1 then (-2:ℝ) else 0)+1 := by
    rcases hf i with h | h <;> norm_num [h]
  have hp (i : ι) : f i = if f i = -1 then (-1:ℝ) else 1 := by
    rcases hf i with h | h <;> norm_num [h]
  refine ⟨d,?_,?_⟩
  · calc
      (∑ i, f i) = ∑ i, ((if f i = -1 then (-2:ℝ) else 0)+1) :=
        Finset.sum_congr rfl (fun i _ => ht i)
      _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_ite,d]; ring
  · calc
      (∏ i, f i) = ∏ i, (if f i = -1 then (-1:ℝ) else 1) :=
        Finset.prod_congr rfl (fun i _ => hp i)
      _ = _ := by simp [Finset.prod_ite,d]

theorem sign_product {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, IsSign (f i)) : IsSign (∏ i, f i) := by
  obtain ⟨d,_,hp⟩ := sign_sum_product_data f hf
  rw [hp,neg_one_pow_eq_ite]
  split_ifs <;> norm_num [IsSign]

theorem sign_sum_mod_four {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, IsSign (f i)) (hp : (∏ i, f i)=1) :
    ∃ k : ℕ, (∑ i, f i) = (Fintype.card ι : ℝ)-4*k := by
  obtain ⟨d,hs,hd⟩ := sign_sum_product_data f hf
  have he : Even d := (neg_one_pow_eq_one_iff_even (by norm_num : (-1:ℝ)≠1)).mp (hd.symm.trans hp)
  obtain ⟨k,hk⟩ := he
  refine ⟨k,?_⟩
  have hk' : (d : ℝ) = k+k := by exact_mod_cast hk
  linarith

/-- Multiplying prescribed columns by signs preserves the complete partial-Hadamard predicate. -/
def columnSwitch {ι κ : Type*} (P : Matrix ι κ ℝ) (e : κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => P i j * e j

theorem columnSwitch_partialHadamard {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (P : Matrix ι κ ℝ) (e : κ → ℝ) (hP : IsPartialHadamard P)
    (he : ∀ j, IsSign (e j)) : IsPartialHadamard (columnSwitch P e) := by
  constructor
  · intro i j
    rcases hP.1 i j with h | h <;> rcases he j with g | g <;>
      norm_num [columnSwitch,IsSign,h,g]
  · ext i k
    have hg := congrArg (fun A => A i k) hP.2
    change (∑ j, P i j * P k j) = (Fintype.card κ : ℝ)*(if i=k then 1 else 0) at hg
    change (∑ j, (P i j * e j)*(P k j * e j)) = _
    calc
      (∑ j, (P i j * e j)*(P k j * e j)) = ∑ j, P i j * P k j := by
        apply Finset.sum_congr rfl
        intro j _
        have hj := isSign_sq (he j)
        calc
          _ = (P i j * P k j)*(e j)^2 := by ring
          _ = _ := by rw [hj]; ring
      _ = _ := hg


/-- Residual norm three bounds every off-diagonal prescribed column correlation. -/
theorem codimension_three_column_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι (Fin 3 ⊕ ι) ℝ) (hP : IsPartialHadamard P) :
    ∀ j k : Fin 3 ⊕ ι, j ≠ k →
      -3 ≤ (∑ i, P i j * P i k) ∧ (∑ i, P i j * P i k) ≤ 3 := by
  classical
  obtain ⟨H, hHr, hHc, hret⟩ := real_frame_extension P hP.2
  let N : ℝ := Fintype.card (Fin 3 ⊕ ι)
  have hN : 0 < N := by simp [N]; positivity
  have hNval : N = (Fintype.card ι : ℝ)+3 := by simp [N]; ring
  let r : (Fin 3 ⊕ ι) → EuclideanSpace ℝ (Fin 3) :=
    fun j => WithLp.toLp 2 (fun i => H (Sum.inl i) j)
  have hinner (j k : Fin 3 ⊕ ι) :
      inner ℝ (r j) (r k) + (∑ i, P i j * P i k) = N * (if j=k then 1 else 0) := by
    have hg := congrArg (fun A => A k j) hHc
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, Fintype.sum_sum_type] at hg
    simp_rw [hret] at hg
    change (∑ i : Fin 3, H (Sum.inl i) k * H (Sum.inl i) j) +
      (∑ i, P i j * P i k) = _
    simpa only [mul_comm,eq_comm] using hg
  have hrnorm (j : Fin 3 ⊕ ι) : inner ℝ (r j) (r j) = 3 := by
    have hs : (∑ i, P i j * P i j) = (Fintype.card ι : ℝ) := by
      have hterm : ∀ i, P i j * P i j = 1 := by
        intro i
        have hh := isSign_sq (hP.1 i j)
        nlinarith
      simp [hterm]
    have hi := hinner j j
    rw [hs] at hi
    simp only [ite_true,mul_one] at hi
    linarith
  intro j k hjk
  have hi := hinner j k
  simp only [hjk,ite_false,mul_zero] at hi
  have hp := real_inner_self_nonneg (x := r j + r k)
  have hm := real_inner_self_nonneg (x := r j - r k)
  rw [inner_add_left,inner_add_right,inner_add_right,hrnorm j,hrnorm k,
    real_inner_comm (r k) (r j)] at hp
  rw [inner_sub_left,inner_sub_right,inner_sub_right,hrnorm j,hrnorm k,
    real_inner_comm (r k) (r j)] at hm
  have hcomm := real_inner_comm (r j) (r k)
  constructor <;> nlinarith


/-- Classical codimension-three completion, proved by parity switching and tetrahedral geometry. -/
theorem codimension_three_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hdiv : 4 ∣ Fintype.card (Fin 3 ⊕ ι))
    (P : Matrix ι (Fin 3 ⊕ ι) ℝ) (hP : IsPartialHadamard P) :
    ∃ L : Matrix (Fin 3 ⊕ ι) (Fin 3 ⊕ ι) ℝ,
      Matrix.IsHadamard L ∧ ∀ i j, L (Sum.inr i) j = P i j := by
  classical
  have hmod : ∃ t : ℕ, Fintype.card ι = 4*t+1 := by
    obtain ⟨m,hm⟩ := hdiv
    have hm' : 3+Fintype.card ι = 4*m := by simpa only [Fintype.card_sum,Fintype.card_fin] using hm
    exact ⟨m-1,by omega⟩
  obtain ⟨t,ht⟩ := hmod
  have hodd : Odd (Fintype.card ι) := ⟨2*t,by omega⟩
  let e : (Fin 3 ⊕ ι) → ℝ := fun j => ∏ i, P i j
  have he (j) : IsSign (e j) := sign_product (fun i => P i j) (fun i => hP.1 i j)
  let Q := columnSwitch P e
  have hQ : IsPartialHadamard Q := columnSwitch_partialHadamard P e hP he
  have hprod (j) : (∏ i, Q i j)=1 := by
    change (∏ i, P i j * e j)=1
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    change e j * (e j)^(Fintype.card ι)=1
    rcases he j with h | h
    · simp [h]
    · rw [h,hodd.neg_one_pow]; norm_num
  have hcross (j k : Fin 3 ⊕ ι) (hjk : j ≠ k) :
      (∑ i, Q i j * Q i k) = -3 ∨ (∑ i, Q i j * Q i k) = 1 := by
    have hsign (i) : IsSign (Q i j * Q i k) := by
      rcases hQ.1 i j with h | h <;> rcases hQ.1 i k with g | g <;>
        norm_num [IsSign,h,g]
    have hp : (∏ i, Q i j * Q i k)=1 := by rw [Finset.prod_mul_distrib,hprod,hprod]; norm_num
    obtain ⟨d,hd⟩ := sign_sum_mod_four (fun i => Q i j * Q i k) hsign hp
    have hb := codimension_three_column_bounds Q hQ j k hjk
    have ht' : (Fintype.card ι : ℝ)=4*t+1 := by exact_mod_cast ht
    have hlow : (4 : ℝ)*t ≤ 4*d+2 := by nlinarith [hb.2]
    have hlowN : 4*t ≤ 4*d+2 := by exact_mod_cast hlow
    have hhigh : (d : ℝ) ≤ t+1 := by nlinarith [hb.1]
    have hlow' : t ≤ d := by omega
    have hhigh' : d ≤ t+1 := by exact_mod_cast hhigh
    have hcases : d=t ∨ d=t+1 := by omega
    rcases hcases with h | h
    · exact Or.inr (by rw [h] at hd; nlinarith)
    · exact Or.inl (by rw [h] at hd; push_cast at hd; nlinarith)
  obtain ⟨H,hH,hret⟩ := tetrahedral_completion Q hQ hcross
  have hHp : IsPartialHadamard H := by
    constructor
    · intro i j
      exact Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j)
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hH.mul_conjTranspose
  refine ⟨columnSwitch H e,isHadamard_mathlib (columnSwitch_partialHadamard H e hHp he),?_⟩
  intro i j
  change H (Sum.inr i) j * e j = P i j
  rw [hret]
  change (P i j * e j)*e j = P i j
  rcases he j with h | h <;> simp [h]

/-- Column-index-independent version, preserving the original rows through an injection. -/
theorem codimension_three_completion_of_card {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι + 3)
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (hdiv : 4 ∣ Fintype.card κ) :
    ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ),
      Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  classical
  let e : (Fin 3 ⊕ ι) ≃ κ := Fintype.equivOfCardEq (by simp [hcard]; omega)
  let P' : Matrix ι (Fin 3 ⊕ ι) ℝ := P.submatrix id e
  have hP' : IsPartialHadamard P' := by
    constructor
    · intro i j
      exact hP.1 i (e j)
    · change P.submatrix id e * (Pᵀ).submatrix e id =
        (Fintype.card (Fin 3 ⊕ ι) : ℝ) • 1
      rw [Matrix.submatrix_mul_equiv]
      simpa only [Matrix.submatrix_id_id, Fintype.card_congr e] using hP.2
  have hdiv' : 4 ∣ Fintype.card (Fin 3 ⊕ ι) := by simpa only [Fintype.card_congr e] using hdiv
  obtain ⟨H,hH,hret⟩ := codimension_three_completion hdiv' P' hP'
  let rows : ι ↪ κ := ⟨fun i => e (Sum.inr i), e.injective.comp Sum.inr_injective⟩
  refine ⟨Matrix.reindex e e H, rows, hH.reindex e e, ?_⟩
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, rows,
    Function.Embedding.coeFn_mk, e.symm_apply_apply, hret, P', id_eq, e.apply_symm_apply]
    using hret i (e.symm j)


/-- Equal row and column cardinalities already give a full Hadamard after reindexing. -/
theorem codimension_zero_completion {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hcard : Fintype.card κ = Fintype.card ι)
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) :
    ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ),
      Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  classical
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard.symm
  let L : Matrix κ κ ℝ := P.submatrix e.symm id
  have hL : IsPartialHadamard L := by
    constructor
    · intro i j
      exact hP.1 (e.symm i) j
    · ext i j
      change (∑ k, P (e.symm i) k * P (e.symm j) k) =
        (Fintype.card κ : ℝ)*(if i=j then 1 else 0)
      have hg := congrArg (fun A => A (e.symm i) (e.symm j)) hP.2
      simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,
        Matrix.one_apply,smul_eq_mul,e.symm.injective.eq_iff] using hg
  refine ⟨L,e.toEmbedding,isHadamard_mathlib hL,?_⟩
  intro i j
  simp [L,Matrix.submatrix]

/-- Every positive-order partial Hadamard with at most three missing rows completes. -/
theorem codimension_le_three_completion {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : ℕ) (hr : r ≤ 3) (hcard : Fintype.card κ = Fintype.card ι+r)
    (hdiv : 4 ∣ Fintype.card κ)
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P) :
    ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ),
      Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  interval_cases r
  · exact codimension_zero_completion (by simpa using hcard) P hP
  · exact codimension_one_completion_of_card hcard P hP
  · have heven : Even (Fintype.card ι) := by
      obtain ⟨m,hm⟩ := hdiv
      exact ⟨2*m-1,by omega⟩
    exact codimension_two_completion_of_card hcard P hP heven
  · exact codimension_three_completion_of_card hcard P hP hdiv

end EntropyDesigns.Completion
