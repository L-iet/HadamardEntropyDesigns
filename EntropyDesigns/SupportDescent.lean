module

public import EntropyDesigns.SupportRestriction

/-! # Strict collision ascent with decreasing actual support -/

@[expose] public section
namespace EntropyDesigns

theorem active_support_deletion {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (hfeasible : A.mulVec p = b)
    (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1)
    (hdep : ¬ LinearIndependent ℝ (A.submatrix id (fun a : activeSupport p => (a : α))).col) :
    ∃ q : α → ℝ, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
      collision p < collision q ∧ activeSupport q ⊆ activeSupport p ∧
      (activeSupport q).card < (activeSupport p).card ∧ 0 ≤ lawOverlap p (q - p) := by
  classical
  let S := activeSupport p
  let pS : S → ℝ := fun a => p a
  let AS := A.submatrix id (fun a : S => (a : α))
  have hpositive : ∀ a, 0 < pS a := by
    intro a
    exact lt_of_le_of_ne (hp a) (Ne.symm (Finset.mem_filter.mp a.property).2)
  have hmassS : ∑ a, pS a = 1 := by
    have h := activeSupport_sum p (fun _ => 1)
    simp only [mul_one] at h
    exact h.trans hmass
  have hfeasibleS : AS.mulVec pS = b := by
    funext i
    have hsum := activeSupport_sum p (fun a => A i a)
    have hi := congrFun hfeasible i
    simpa [AS, pS, S, Matrix.mulVec, dotProduct, mul_comm] using hsum.trans
      (by simpa [Matrix.mulVec, dotProduct, mul_comm] using hi)
  obtain ⟨w, hw, hmassw, hAw, hcollisionw, hcardw, horientationw⟩ :=
    dependent_support_deletion AS b pS hpositive hmassS hfeasibleS i₀
      (fun a => hconstant a) hdep
  let q := extendWeights S w
  have hcollisionp : collision pS = collision p := by
    simpa [collision, pS, S, pow_two] using activeSupport_sum p p
  have hcollisionq : collision q = collision w :=
    extendWeights_sum S w (fun x => x ^ 2) (by norm_num)
  refine ⟨q, extendWeights_nonneg S w hw, ?_, ?_, ?_,
    extendWeights_support_subset S w, ?_, ?_⟩
  · exact (extendWeights_sum S w id rfl).trans hmassw
  · funext i
    have hsum := extendWeights_moment S w (fun a => A i a)
    have hi := congrFun hAw i
    simpa [q, Matrix.mulVec, dotProduct, AS, mul_comm] using hsum.trans
      (by simpa [Matrix.mulVec, dotProduct, AS, mul_comm] using hi)
  · rw [hcollisionq, ← hcollisionp]
    exact hcollisionw
  · rw [extendWeights_support_card S w]
    change (activeSupport w).card < S.card
    simpa only [activeSupport, Fintype.card_coe] using hcardw
  · have hcross : lawOverlap p q = lawOverlap pS w := by
      simpa [lawOverlap, mul_comm] using extendWeights_moment S w p
    rwa [lawOverlap_sub, lawOverlap_self, hcross, ← hcollisionp,
      ← lawOverlap_self, ← lawOverlap_sub]

theorem independent_support_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : ∑ a, p a = 1) (hfeasible : A.mulVec p = b)
    (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ q : α → ℝ, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
      collision p ≤ collision q ∧ activeSupport q ⊆ activeSupport p ∧
      LinearIndependent ℝ (A.submatrix id (fun a : activeSupport q => (a : α))).col := by
  classical
  have h : ∀ m : ℕ, ∀ p : α → ℝ, (activeSupport p).card = m →
      (∀ a, 0 ≤ p a) → (∑ a, p a = 1) → A.mulVec p = b →
      ∃ q : α → ℝ, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧ A.mulVec q = b ∧
        collision p ≤ collision q ∧ activeSupport q ⊆ activeSupport p ∧
        LinearIndependent ℝ (A.submatrix id (fun a : activeSupport q => (a : α))).col := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hcard hp hmass hfeasible
      by_cases hlin : LinearIndependent ℝ
          (A.submatrix id (fun a : activeSupport p => (a : α))).col
      · exact ⟨p, hp, hmass, hfeasible, le_rfl, Finset.Subset.refl _, hlin⟩
      · obtain ⟨q, hq, hmq, hAq, hCq, hsubq, hcardq, _⟩ :=
          active_support_deletion A b p hp hmass hfeasible i₀ hconstant hlin
        obtain ⟨w, hw, hmw, hAw, hCw, hsubw, hlinw⟩ :=
          ih (activeSupport q).card (by omega) q rfl hq hmq hAq
        exact ⟨w, hw, hmw, hAw, hCq.le.trans hCw, hsubw.trans hsubq, hlinw⟩
  exact h (activeSupport p).card p rfl hp hmass hfeasible

theorem independent_support_card_bound {ι α : Type*} [Fintype ι] [Fintype α]
    (A : Matrix ι α ℝ) (q : α → ℝ)
    (hlin : LinearIndependent ℝ (A.submatrix id (fun a : activeSupport q => (a : α))).col) :
    (activeSupport q).card ≤ Fintype.card ι := by
  simpa only [Fintype.card_coe, Module.finrank_pi, Module.finrank_self, mul_one] using
    hlin.fintype_card_le_finrank

end EntropyDesigns
