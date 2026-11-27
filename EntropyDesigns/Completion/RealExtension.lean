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

/-- Extend any real scaled orthonormal row family by exactly the missing rows. -/
theorem real_frame_extension {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (W : Matrix ι (κ ⊕ ι) ℝ)
    (hW : W * Wᵀ = (Fintype.card (κ ⊕ ι) : ℝ) • 1) :
    ∃ H : Matrix (κ ⊕ ι) (κ ⊕ ι) ℝ,
      H * Hᵀ = (Fintype.card (κ ⊕ ι) : ℝ) • 1 ∧
      Hᵀ * H = (Fintype.card (κ ⊕ ι) : ℝ) • 1 ∧
      ∀ i j, H (Sum.inr i) j = W i j := by
  classical
  let N : ℝ := Fintype.card (κ ⊕ ι)
  have hN : 0 < N := by
    change (0 : ℝ) < (Fintype.card (κ ⊕ ι) : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (κ ⊕ ι))
  have hs : Real.sqrt N ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hN)
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (le_of_lt hN)
  let v : κ ⊕ ι → EuclideanSpace ℝ (κ ⊕ ι) :=
    fun i => WithLp.toLp 2 (fun j => Sum.elim (fun _ => 0) (fun k => W k j / Real.sqrt N) i)
  let s : Set (κ ⊕ ι) := Set.range Sum.inr
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    dsimp only [s]
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, ⟨a, rfl⟩⟩
    rcases j with ⟨j, ⟨b, rfl⟩⟩
    have hg := congrArg (fun M => M b a) hW
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hg
    simp only [Set.domRestrict_apply, v, PiLp.inner_apply,
      Sum.elim_inr, RCLike.inner_apply, conj_trivial]
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
      exact (Sum.inr.inj (congrArg Subtype.val heq2)).symm
    · simp
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp [finrank_euclideanSpace])

  let U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℝ := fun i j => b i j
  have hU : U * Uᵀ = 1 := by
    ext i j
    change (∑ k, b i k * b j k) = if i = j then 1 else 0
    have h := b.inner_eq_ite j i
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm] using h
  have hUc : Uᵀ * U = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hU
  let H : Matrix (κ ⊕ ι) (κ ⊕ ι) ℝ := Real.sqrt N • U
  have hH : H * Hᵀ = N • 1 := by
    simp [H, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hU,
      smul_smul, hsq]
  have hHc : Hᵀ * H = N • 1 := by
    simp [H, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hUc,
      smul_smul, hsq]
  have hret : ∀ i j, H (Sum.inr i) j = W i j := by
    intro i j
    have he := congrArg (fun x : EuclideanSpace ℝ (κ ⊕ ι) => x j)
      (hb (Sum.inr i) ⟨i, rfl⟩)
    change b (Sum.inr i) j = W i j / Real.sqrt N at he
    change Real.sqrt N * b (Sum.inr i) j = W i j
    rw [he]
    field_simp
  exact ⟨H, hH, hHc, hret⟩
end EntropyDesigns.Completion
