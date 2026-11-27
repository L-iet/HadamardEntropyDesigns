/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import EntropyDesigns.Completion.RealExtension
@[expose] public section
namespace EntropyDesigns.Completion
open Matrix

/-- Distinct radius-squared-three vectors with mutual inner product minus one number at most four. -/
theorem tetrahedral_card_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset E) (hnorm : ∀ x ∈ s, inner ℝ x x = 3)
    (hcross : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → inner ℝ x y = -1) : s.card ≤ 4 := by
  classical
  have hrow (x : E) (hx : x ∈ s) : inner ℝ x (∑ y ∈ s, y) = 4-(s.card : ℝ) := by
    rw [inner_sum]
    calc
      (∑ y ∈ s, inner ℝ x y) = ∑ y ∈ s, ((if y=x then (4:ℝ) else 0)-1) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases h : y=x
        · subst y; rw [hnorm x hx]; norm_num
        · simp [h, hcross x hx y hy (Ne.symm h)]
      _ = _ := by simp [Finset.sum_sub_distrib,hx]
  have henergy : inner ℝ (∑ x ∈ s, x) (∑ x ∈ s, x) =
      (s.card : ℝ) * (4-s.card) := by
    rw [sum_inner]
    calc
      (∑ x ∈ s, inner ℝ x (∑ y ∈ s, y)) = ∑ _ ∈ s, (4-(s.card : ℝ)) :=
        Finset.sum_congr rfl (fun x hx => hrow x hx)
      _ = _ := by simp; ring
  have hnonneg := real_inner_self_nonneg (x := ∑ x ∈ s, x)
  rw [henergy] at hnonneg
  by_contra h
  have hh : (5 : ℕ) ≤ s.card := by omega
  have hh' : (5 : ℝ) ≤ s.card := by exact_mod_cast hh
  nlinarith

/-- The four vertices of a real sign tetrahedron. -/
def signTetrahedron : Matrix (Fin 3) (Fin 4) ℝ :=
  !![1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]

theorem signTetrahedron_sign (i : Fin 3) (j : Fin 4) : IsSign (signTetrahedron i j) := by
  fin_cases i <;> fin_cases j <;> norm_num [signTetrahedron,IsSign]

theorem signTetrahedron_gram (j k : Fin 4) :
    (∑ i : Fin 3, signTetrahedron i j * signTetrahedron i k) =
      if j=k then 3 else -1 := by
  fin_cases j <;> fin_cases k <;> norm_num [signTetrahedron,Fin.sum_univ_succ]


/-- A radius-three Gram configuration with correlations three or minus one has a three-row sign factor. -/
theorem tetrahedral_sign_factor {κ : Type*} [Fintype κ]
    (r : κ → EuclideanSpace ℝ (Fin 3))
    (hnorm : ∀ j, inner ℝ (r j) (r j) = 3)
    (hcross : ∀ j k, inner ℝ (r j) (r k) = 3 ∨ inner ℝ (r j) (r k) = -1) :
    ∃ B : Matrix (Fin 3) κ ℝ, IsSignMatrix B ∧
      Bᵀ * B = fun j k => inner ℝ (r j) (r k) := by
  classical
  have same (j k : κ) (h : inner ℝ (r j) (r k) = 3) : r j = r k := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hc : inner ℝ (r k) (r j) = 3 := by simpa only [real_inner_comm] using h
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      hnorm j, hnorm k, h, hc]
    norm_num
  let s : Finset (EuclideanSpace ℝ (Fin 3)) := Finset.univ.image r
  have hs (j : κ) : r j ∈ s := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hsnorm : ∀ x ∈ s, inner ℝ x x = 3 := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact hnorm j
  have hsdiff : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → inner ℝ x y = -1 := by
    intro x hx y hy hxy
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hy
    rcases hcross j k with h | h
    · exact (hxy (same j k h)).elim
    · exact h
  have hcard : Fintype.card ↥s ≤ 4 := by
    simpa using tetrahedral_card_le s hsnorm hsdiff
  let e : ↥s → Fin 4 := fun x => Fin.castLE hcard ((Fintype.equivFin ↥s) x)
  have he : Function.Injective e := by
    intro x y h
    apply (Fintype.equivFin ↥s).injective
    apply Fin.ext
    have hv := congrArg (fun x : Fin 4 => x.val) h
    exact hv
  let c : κ → Fin 4 := fun j => e ⟨r j, hs j⟩
  have hc (j k : κ) : c j = c k ↔ r j = r k := by
    constructor
    · intro h
      exact congrArg Subtype.val (he h)
    · intro h
      exact congrArg e (Subtype.ext h)
  let B : Matrix (Fin 3) κ ℝ := fun i j => signTetrahedron i (c j)
  refine ⟨B, (fun i j => signTetrahedron_sign i (c j)), ?_⟩
  ext j k
  change (∑ i, signTetrahedron i (c j) * signTetrahedron i (c k)) = _
  rw [signTetrahedron_gram]
  simp only [hc]
  by_cases h : r j = r k
  · rw [if_pos h, h]
    exact (hnorm k).symm
  · rw [if_neg h]
    exact (hsdiff (r j) (hs j) (r k) (hs k) h).symm


/-- Reverse a nonsingular scalar square Gram identity. -/
theorem reverse_scalar_gram {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : Matrix κ κ ℝ) (N : ℝ) (hN : N ≠ 0) (h : Lᵀ * L = N • 1) :
    L * Lᵀ = N • 1 := by
  have hl : (N⁻¹ • Lᵀ) * L = 1 := by simp [smul_mul_assoc,h,smul_smul,hN]
  have hr : L * (N⁻¹ • Lᵀ) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hl
  have hscale := congrArg (fun A : Matrix κ κ ℝ => N • A) hr
  simpa only [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hN, one_smul] using hscale

/-- Codimension-three completion for the switched {-3,1} column-correlation class. -/
theorem tetrahedral_completion {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι (Fin 3 ⊕ ι) ℝ) (hP : IsPartialHadamard P)
    (hcross : ∀ j k : Fin 3 ⊕ ι, j ≠ k →
      (∑ i, P i j * P i k) = -3 ∨ (∑ i, P i j * P i k) = 1) :
    ∃ L : Matrix (Fin 3 ⊕ ι) (Fin 3 ⊕ ι) ℝ,
      Matrix.IsHadamard L ∧ ∀ i j, L (Sum.inr i) j = P i j := by
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
  have hrcross (j k : Fin 3 ⊕ ι) :
      inner ℝ (r j) (r k) = 3 ∨ inner ℝ (r j) (r k) = -1 := by
    by_cases hjk : j=k
    · subst k; exact Or.inl (hrnorm j)
    · have hi := hinner j k
      simp only [hjk,ite_false,mul_zero] at hi
      rcases hcross j k hjk with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  obtain ⟨B,hBsign,hBgram⟩ := tetrahedral_sign_factor r hrnorm hrcross
  let L : Matrix (Fin 3 ⊕ ι) (Fin 3 ⊕ ι) ℝ :=
    fun i j => Sum.elim (fun a => B a j) (fun a => P a j) i
  have hLsign : IsSignMatrix L := by
    intro i j
    cases i with
    | inl i => exact hBsign i j
    | inr i => exact hP.1 i j
  have hLc : Lᵀ * L = N • 1 := by
    ext j k
    have hb := congrArg (fun A => A j k) hBgram
    simp only [Matrix.mul_apply,Matrix.transpose_apply] at hb
    change (∑ i : Fin 3 ⊕ ι, L i j * L i k) = N * (if j=k then 1 else 0)
    simp only [Fintype.sum_sum_type,L,Sum.elim_inl,Sum.elim_inr]
    rw [hb]
    exact hinner j k
  refine ⟨L,isHadamard_mathlib ⟨hLsign,reverse_scalar_gram L N (ne_of_gt hN) hLc⟩,?_⟩
  intro i j
  rfl


/-- Column-index-independent version, preserving the original rows through an injection. -/
theorem tetrahedral_completion_of_card {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι + 3)
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
    (hcross : ∀ j k : κ, j ≠ k →
      (∑ i, P i j * P i k) = -3 ∨ (∑ i, P i j * P i k) = 1) :
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
  have hc' : ∀ j k : Fin 3 ⊕ ι, j ≠ k →
      (∑ i, P' i j * P' i k) = -3 ∨ (∑ i, P' i j * P' i k) = 1 := by
    intro j k hjk
    exact hcross (e j) (e k) (fun h => hjk (e.injective h))
  obtain ⟨H,hH,hret⟩ := tetrahedral_completion P' hP' hc'
  let rows : ι ↪ κ := ⟨fun i => e (Sum.inr i), e.injective.comp Sum.inr_injective⟩
  refine ⟨Matrix.reindex e e H, rows, hH.reindex e e, ?_⟩
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, rows,
    Function.Embedding.coeFn_mk, e.symm_apply_apply, hret, P', id_eq, e.apply_symm_apply]
    using hret i (e.symm j)

end EntropyDesigns.Completion
