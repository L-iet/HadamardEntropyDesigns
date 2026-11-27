module

public import EntropyDesigns.SupportVertex

/-! # Each reduction is the stated minimum-ratio endpoint algorithm -/

@[expose] public section
namespace EntropyDesigns

theorem reductionStep_exact_endpoint {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p q : α → ℝ)
    (hp : feasibleLaw A b p) (hstep : reductionStep A b p q) :
    ∃ z : α → ℝ, z ≠ 0 ∧ A.mulVec z = 0 ∧ 0 ≤ lawOverlap p z ∧
      q = (fun a => p a + z a) ∧
      (∀ a, z a < 0 → 1 ≤ p a / (-z a)) ∧
      (∃ a, z a < 0 ∧ p a / (-z a) = 1) := by
  classical
  refine ⟨q - p, ?_, ?_, hstep.2.2.2.2, ?_, ?_, ?_⟩
  · intro hz
    have hqp : q = p := sub_eq_zero.mp hz
    have h := hstep.2.1
    simpa [hqp] using h
  · rw [Matrix.mulVec_sub, hstep.1.2.2, hp.2.2, sub_self]
  · funext a
    simp
  · intro a ha
    apply (le_div_iff₀ (neg_pos.mpr ha)).2
    dsimp only [Pi.sub_apply]
    linarith [hstep.1.1 a]
  · have hreverse : ¬ activeSupport p ⊆ activeSupport q := by
      intro h
      have := Finset.card_le_card h
      have := hstep.2.2.2.1
      omega
    obtain ⟨a, hap, haq⟩ := Finset.not_subset.mp hreverse
    have hpa : 0 < p a := lt_of_le_of_ne (hp.1 a)
      (Ne.symm (Finset.mem_filter.mp hap).2)
    have hqa : q a = 0 := by simpa [activeSupport] using haq
    refine ⟨a, ?_, ?_⟩
    · simpa [hqa] using neg_neg_of_pos hpa
    · simp [hqa, hpa.ne']

theorem reductionStep_interpolation {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (b : ι → ℝ) (p q : α → ℝ)
    (hp : feasibleLaw A b p) (hstep : reductionStep A b p q) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
      feasibleLaw A b (fun a => p a + u * (q - p) a)) ∧
    MonotoneOn (fun u : ℝ => collision (fun a => p a + u * (q - p) a)) (Set.Ici 0) := by
  refine ⟨?_, collision_direction_monotone p (q - p) hstep.2.2.2.2⟩
  intro u hu hu'
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have h1 := mul_nonneg (by linarith : 0 ≤ 1 - u) (hp.1 a)
    have h2 := mul_nonneg hu (hstep.1.1 a)
    dsimp only [Pi.sub_apply]
    nlinarith
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
      hp.2.1, hstep.1.2.1]
  · change A.mulVec (p + u • (q - p)) = b
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_sub,
      hp.2.2, hstep.1.2.2, sub_self, smul_zero, add_zero]

theorem bounded_vertex_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ k : ℕ, k ≤ (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧
      ∃ path : Fin (k + 1) → (α → ℝ),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        path (Fin.last k) ∈ Set.extremePoints ℝ {q | feasibleLaw A b q} ∧
        (activeSupport (path (Fin.last k))).card ≤ Fintype.card ι := by
  obtain ⟨k, hk, path, hfirst, hsteps, hlast, hlin⟩ :=
    bounded_support_reduction A b p hp i₀ hconstant
  exact ⟨k, hk, path, hfirst, hsteps, independent_support_vertex A b _ hlast hlin,
    independent_support_card_bound A _ hlin⟩

end EntropyDesigns
