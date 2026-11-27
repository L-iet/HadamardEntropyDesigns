/- Copyright (c) 2026 Joshua Mark. Apache-2.0. -/
module
public import EntropyDesigns.Completion.Base
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
namespace EntropyDesigns.Completion
open Matrix

/-- Every rectangular sign frame of real codimension one completes, retaining its rows. -/
theorem codimension_one_completion (n : ℕ)
    (W : Matrix (Fin n) (Option (Fin n)) ℝ) (hW : IsPartialHadamard W) :
    ∃ H : Matrix (Option (Fin n)) (Option (Fin n)) ℝ,
      Matrix.IsHadamard H ∧ ∀ i j, H (some i) j = W i j := by
  classical
  let N : ℝ := Fintype.card (Option (Fin n))
  have hN : 0 < N := by simp [N]; positivity
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN)
  let v : Option (Fin n) → EuclideanSpace ℝ (Option (Fin n)) :=
    fun i => WithLp.toLp 2 (fun j => Option.elim i 0 (fun k => W k j / Real.sqrt N))
  let s : Set (Option (Fin n)) := Set.range some
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    dsimp only [s]
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, ⟨a, rfl⟩⟩
    rcases j with ⟨j, ⟨b, rfl⟩⟩
    have hg := congrArg (fun M => M b a) hW.2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hg
    simp only [Set.domRestrict_apply, v, PiLp.inner_apply,
      Option.elim_some, RCLike.inner_apply, conj_trivial]
    simp only [div_mul_div_comm, ← Finset.sum_div]
    rw [hsq, hg]
    split_ifs with hba heq heq2
    · simpa only [mul_one] using (div_self (ne_of_gt hN))
    · exfalso
      apply heq
      subst b
      rfl
    · exfalso
      apply hba
      exact (Option.some.inj (congrArg Subtype.val heq2)).symm
    · simp
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])

  let U : Matrix (Option (Fin n)) (Option (Fin n)) ℝ := fun i j => b i j
  have hU : U * Uᵀ = 1 := by
    ext i j
    change (∑ k, b i k * b j k) = if i = j then 1 else 0
    have h := b.inner_eq_ite j i
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm] using h
  have hUc : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hU
  let H : Matrix (Option (Fin n)) (Option (Fin n)) ℝ := Real.sqrt N • U
  have hH : H * Hᵀ = N • 1 := by
    simp [H, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU,
      smul_smul, hsq]
  have hHc : Hᵀ * H = N • 1 := by
    simp [H, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hUc,
      smul_smul, hsq]
  have hret : ∀ i j, H (some i) j = W i j := by
    intro i j
    have he := congrArg (fun x : EuclideanSpace ℝ (Option (Fin n)) => x j)
      (hb (some i) ⟨i, rfl⟩)
    change b (some i) j = W i j / Real.sqrt N at he
    change Real.sqrt N * b (some i) j = W i j
    rw [he]
    field_simp
  have hsign : IsSignMatrix H := by
    intro i j
    cases i with
    | some i => rw [hret]; exact hW.1 i j
    | none =>
      have hc := congrArg (fun M => M j j) hHc
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, Fintype.sum_option] at hc
      have hsum : (∑ i : Fin n, H (some i) j * H (some i) j) = n := by
        simp_rw [hret]
        have hz : ∀ i : Fin n, W i j * W i j = 1 := by
          intro i
          have hh := isSign_sq (hW.1 i j)
          nlinarith
        simp [hz]
      rw [hsum] at hc
      have hn : N = (n : ℝ) + 1 := by simp [N]
      have hsq1 : H none j ^ 2 = 1 := by nlinarith
      exact (sq_eq_one_iff).mp hsq1
  exact ⟨H, isHadamard_mathlib ⟨hsign, hH⟩, hret⟩

/-- Every finitely indexed rectangular sign frame of real codimension one completes, retaining its rows. -/
theorem codimension_one_completion_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : Matrix (ι) (Option (ι)) ℝ) (hW : IsPartialHadamard W) :
    ∃ H : Matrix (Option (ι)) (Option (ι)) ℝ,
      Matrix.IsHadamard H ∧ ∀ i j, H (some i) j = W i j := by
  classical
  let N : ℝ := Fintype.card (Option (ι))
  have hN : 0 < N := by simp [N]; positivity
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN)
  let v : Option (ι) → EuclideanSpace ℝ (Option (ι)) :=
    fun i => WithLp.toLp 2 (fun j => Option.elim i 0 (fun k => W k j / Real.sqrt N))
  let s : Set (Option (ι)) := Set.range some
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    dsimp only [s]
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, ⟨a, rfl⟩⟩
    rcases j with ⟨j, ⟨b, rfl⟩⟩
    have hg := congrArg (fun M => M b a) hW.2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hg
    simp only [Set.domRestrict_apply, v, PiLp.inner_apply,
      Option.elim_some, RCLike.inner_apply, conj_trivial]
    simp only [div_mul_div_comm, ← Finset.sum_div]
    rw [hsq, hg]
    split_ifs with hba heq heq2
    · simpa only [mul_one] using (div_self (ne_of_gt hN))
    · exfalso
      apply heq
      subst b
      rfl
    · exfalso
      apply hba
      exact (Option.some.inj (congrArg Subtype.val heq2)).symm
    · simp
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])

  let U : Matrix (Option (ι)) (Option (ι)) ℝ := fun i j => b i j
  have hU : U * Uᵀ = 1 := by
    ext i j
    change (∑ k, b i k * b j k) = if i = j then 1 else 0
    have h := b.inner_eq_ite j i
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm] using h
  have hUc : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hU
  let H : Matrix (Option (ι)) (Option (ι)) ℝ := Real.sqrt N • U
  have hH : H * Hᵀ = N • 1 := by
    simp [H, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU,
      smul_smul, hsq]
  have hHc : Hᵀ * H = N • 1 := by
    simp [H, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hUc,
      smul_smul, hsq]
  have hret : ∀ i j, H (some i) j = W i j := by
    intro i j
    have he := congrArg (fun x : EuclideanSpace ℝ (Option (ι)) => x j)
      (hb (some i) ⟨i, rfl⟩)
    change b (some i) j = W i j / Real.sqrt N at he
    change Real.sqrt N * b (some i) j = W i j
    rw [he]
    field_simp
  have hsign : IsSignMatrix H := by
    intro i j
    cases i with
    | some i => rw [hret]; exact hW.1 i j
    | none =>
      have hc := congrArg (fun M => M j j) hHc
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, Fintype.sum_option] at hc
      have hsum : (∑ i : ι, H (some i) j * H (some i) j) = (Fintype.card ι : ℝ) := by
        simp_rw [hret]
        have hz : ∀ i : ι, W i j * W i j = 1 := by
          intro i
          have hh := isSign_sq (hW.1 i j)
          nlinarith
        simp [hz]
      rw [hsum] at hc
      have hn : N = (Fintype.card ι : ℝ) + 1 := by simp [N]
      have hsq1 : H none j ^ 2 = 1 := by nlinarith
      exact (sq_eq_one_iff).mp hsq1
  exact ⟨H, isHadamard_mathlib ⟨hsign, hH⟩, hret⟩

/-- Column-index-independent version, preserving the original rows through an injection. -/
theorem codimension_one_completion_of_card {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hcard : Fintype.card κ = Fintype.card ι + 1)
    (P : Matrix ι κ ℝ) (hP : IsPartialHadamard P)
:
    ∃ (L : Matrix κ κ ℝ) (rows : ι ↪ κ),
      Matrix.IsHadamard L ∧ ∀ i j, L (rows i) j = P i j := by
  classical
  let e : (Option ι) ≃ κ := Fintype.equivOfCardEq (by simp [hcard])
  let P' : Matrix ι (Option ι) ℝ := P.submatrix id e
  have hP' : IsPartialHadamard P' := by
    constructor
    · intro i j
      exact hP.1 i (e j)
    · change P.submatrix id e * (Pᵀ).submatrix e id =
        (Fintype.card (Option ι) : ℝ) • 1
      rw [Matrix.submatrix_mul_equiv]
      simpa only [Matrix.submatrix_id_id, Fintype.card_congr e] using hP.2
  obtain ⟨H,hH,hret⟩ := codimension_one_completion_general P' hP'
  let rows : ι ↪ κ := ⟨fun i => e (some i), e.injective.comp (Option.some_injective ι)⟩
  refine ⟨Matrix.reindex e e H, rows, hH.reindex e e, ?_⟩
  intro i j
  simpa only [Matrix.reindex_apply, Matrix.submatrix_apply, rows,
    Function.Embedding.coeFn_mk, e.symm_apply_apply, hret, P', id_eq, e.apply_symm_apply]
    using hret i (e.symm j)

end EntropyDesigns.Completion

