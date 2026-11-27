module

public import EntropyDesigns.SupportDescent

/-! # The exact dimension of feasible directions on a finite support -/

@[expose] public section
namespace EntropyDesigns

def supportedKernel {ι α : Type*} [Fintype α] (A : Matrix ι α ℝ)
    (S : Finset α) : Submodule ℝ (α → ℝ) where
  carrier := {z | A.mulVec z = 0 ∧ ∀ a, a ∉ S → z a = 0}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    intro z w hz hw
    exact ⟨by simp [Matrix.mulVec_add, hz.1, hw.1],
      fun a ha => by simp [hz.2 a ha, hw.2 a ha]⟩
  smul_mem' := by
    intro c z hz
    exact ⟨by simp [Matrix.mulVec_smul, hz.1], fun a ha => by simp [hz.2 a ha]⟩

theorem matrix_extendWeights {ι α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix ι α ℝ) (S : Finset α) (w : S → ℝ) :
    A.mulVec (extendWeights S w) = (A.submatrix id (fun a : S => (a : α))).mulVec w := by
  funext i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using
    extendWeights_moment S w (fun a => A i a)

theorem extendWeights_restrict {α : Type*} [DecidableEq α]
    (S : Finset α) (z : α → ℝ) (hz : ∀ a, a ∉ S → z a = 0) :
    extendWeights S (fun a => z a) = z := by
  funext a
  by_cases ha : a ∈ S <;> simp [extendWeights, ha, hz a]

theorem supportedKernel_dimension {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (S : Finset α) :
    Module.finrank ℝ (supportedKernel A S) =
      S.card - (A.submatrix id (fun a : S => (a : α))).rank := by
  classical
  let AS := A.submatrix id (fun a : S => (a : α))
  let K := LinearMap.ker AS.mulVecLin
  let E : K →ₗ[ℝ] supportedKernel A S := {
    toFun := fun w => ⟨extendWeights S w, by
      constructor
      · rw [matrix_extendWeights]
        exact w.property
      · intro a ha
        simp [extendWeights, ha]⟩
    map_add' := by
      intro w v
      apply Subtype.ext
      funext a
      by_cases ha : a ∈ S <;> simp [extendWeights, ha]
    map_smul' := by
      intro c w
      apply Subtype.ext
      funext a
      by_cases ha : a ∈ S <;> simp [extendWeights, ha] }
  have hinj : Function.Injective E := by
    intro w v h
    apply Subtype.ext
    funext a
    have hi := congrArg (fun z : supportedKernel A S => z.val a) h
    simpa [E, extendWeights_on] using hi
  have hsurj : Function.Surjective E := by
    intro z
    have hext : extendWeights S (fun a => z.val a) = z.val :=
      extendWeights_restrict S z.val z.property.2
    have hker : (fun a : S => z.val a) ∈ K := by
      change AS.mulVec (fun a => z.val a) = 0
      rw [← matrix_extendWeights, hext]
      exact z.property.1
    refine ⟨⟨fun a => z.val a, hker⟩, ?_⟩
    apply Subtype.ext
    exact hext
  have hdim := (LinearEquiv.ofBijective E ⟨hinj, hsurj⟩).finrank_eq
  have hrank := AS.mulVecLin.finrank_range_add_finrank_ker
  have hsum : AS.rank + Module.finrank ℝ K = S.card := by
    simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self,
      mul_one, Fintype.card_coe] using hrank
  change Module.finrank ℝ (supportedKernel A S) = S.card - AS.rank
  omega

theorem supportedKernel_mono {ι α : Type*} [Fintype α]
    (A : Matrix ι α ℝ) (S T : Finset α) (hST : S ⊆ T) :
    supportedKernel A S ≤ supportedKernel A T := by
  intro z hz
  exact ⟨hz.1, fun a ha => hz.2 a (fun h => ha (hST h))⟩

theorem support_dimension_strict_drop {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (p q : α → ℝ)
    (hfeasible : A.mulVec p = A.mulVec q)
    (hsub : activeSupport q ⊆ activeSupport p)
    (hcard : (activeSupport q).card < (activeSupport p).card) :
    (activeSupport q).card -
        (A.submatrix id (fun a : activeSupport q => (a : α))).rank <
      (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank := by
  classical
  have hreverse : ¬ activeSupport p ⊆ activeSupport q := by
    intro h
    have := Finset.card_le_card h
    omega
  obtain ⟨a, hap, haq⟩ := Finset.not_subset.mp hreverse
  have hpa : p a ≠ 0 := (Finset.mem_filter.mp hap).2
  have hqa : q a = 0 := by simpa [activeSupport] using haq
  have hv : p - q ∈ supportedKernel A (activeSupport p) := by
    constructor
    · rw [Matrix.mulVec_sub, hfeasible, sub_self]
    · intro x hx
      have hpx : p x = 0 := by simpa [activeSupport] using hx
      have hqx : q x = 0 := by
        have hnot : x ∉ activeSupport q := fun h => hx (hsub h)
        simpa [activeSupport] using hnot
      simp [hpx, hqx]
  have hnot : p - q ∉ supportedKernel A (activeSupport q) := by
    intro h
    have hzero := h.2 a haq
    have : p a = 0 := by simpa [hqa] using hzero
    exact hpa this
  have hlt : supportedKernel A (activeSupport q) < supportedKernel A (activeSupport p) := by
    refine lt_of_le_of_ne (supportedKernel_mono A _ _ hsub) ?_
    intro heq
    exact hnot (heq.symm ▸ hv)
  rw [← supportedKernel_dimension, ← supportedKernel_dimension]
  exact Submodule.finrank_lt_finrank_of_lt hlt

end EntropyDesigns
