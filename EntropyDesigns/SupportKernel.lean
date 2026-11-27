module

public import EntropyDesigns.PositiveCorrection

/-! # Oriented kernel directions from dependent moment columns -/

@[expose] public section
namespace EntropyDesigns

theorem dependent_columns_kernel {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (hdep : ¬ LinearIndependent ℝ A.col) :
    ∃ z : α → ℝ, z ≠ 0 ∧ A.mulVec z = 0 := by
  classical
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨z, hlinear, a, ha⟩ := hdep
  refine ⟨z, ?_, ?_⟩
  · intro h
    exact ha (congrFun h a)
  · funext r
    have h := congrFun hlinear r
    simpa [Matrix.mulVec, dotProduct, Matrix.col, Finset.sum_apply, mul_comm] using h

theorem oriented_kernel_direction {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (p : α → ℝ)
    (hdep : ¬ LinearIndependent ℝ A.col) :
    ∃ z : α → ℝ, z ≠ 0 ∧ A.mulVec z = 0 ∧ 0 ≤ lawOverlap p z := by
  obtain ⟨z, hz, hkernel⟩ := dependent_columns_kernel A hdep
  by_cases h : 0 ≤ lawOverlap p z
  · exact ⟨z, hz, hkernel, h⟩
  · refine ⟨-z, ?_, ?_, ?_⟩
    · simpa using hz
    · simpa [Matrix.mulVec_neg] using congrArg Neg.neg hkernel
    · have hneg : lawOverlap p (-z) = -lawOverlap p z := by
        simp [lawOverlap, Finset.sum_neg_distrib]
      rw [hneg]
      linarith

theorem dependent_support_deletion {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : ∀ a, 0 < p a) (hmass : ∑ a, p a = 1) (hfeasible : A.mulVec p = b)
    (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1)
    (hdep : ¬ LinearIndependent ℝ A.col) :
    ∃ q : α → ℝ, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
      collision p < collision q ∧ (Finset.univ.filter (fun a => q a ≠ 0)).card < Fintype.card α ∧
      0 ≤ lawOverlap p (q - p) := by
  classical
  obtain ⟨z, hz, hkernel, horient⟩ := oriented_kernel_direction A p hdep
  have hsum : ∑ a, z a = 0 := by
    have h := congrFun hkernel i₀
    simpa [Matrix.mulVec, dotProduct, hconstant] using h
  have hmoment : ∀ i, ∑ a, p a * A i a = b i := by
    intro i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hfeasible i
  have hzero : ∀ i, ∑ a, z a * A i a = 0 := by
    intro i
    simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hkernel i
  obtain ⟨t, ht, hq, hkill, hmassq, hmomentq, hcollision, _, horientation⟩ :=
    support_reduction_step p z (fun i a => A i a) b hp hmass hz hsum hmoment hzero horient
  let q := fun a => p a + t * z a
  refine ⟨q, hq, hmassq, ?_, hcollision, ?_, horientation⟩
  · funext i
    simpa [q, Matrix.mulVec, dotProduct, mul_comm] using hmomentq i
  · obtain ⟨a, ha⟩ := hkill
    have hproper : Finset.univ.filter (fun a => q a ≠ 0) ⊂ Finset.univ := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      intro heq
      have ha' : a ∈ Finset.univ.filter (fun a => q a ≠ 0) := by rw [heq]; exact Finset.mem_univ a
      exact (Finset.mem_filter.mp ha').2 ha
    simpa using Finset.card_lt_card hproper

end EntropyDesigns
