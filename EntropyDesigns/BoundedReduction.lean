module

public import EntropyDesigns.SupportDimension

/-! # A support-reduction sequence with the exact face-dimension bound -/

@[expose] public section
namespace EntropyDesigns

def feasibleLaw {ι α : Type*} [Fintype α] (A : Matrix ι α ℝ)
    (b : ι → ℝ) (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧ A.mulVec p = b

def reductionStep {ι α : Type*} [Fintype α] (A : Matrix ι α ℝ)
    (b : ι → ℝ) (p q : α → ℝ) : Prop :=
  feasibleLaw A b q ∧ collision p < collision q ∧
    activeSupport q ⊆ activeSupport p ∧ (activeSupport q).card < (activeSupport p).card ∧
    0 ≤ lawOverlap p (q - p)

theorem bounded_support_reduction {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (A : Matrix ι α ℝ) (b : ι → ℝ) (p : α → ℝ)
    (hp : feasibleLaw A b p) (i₀ : ι) (hconstant : ∀ a, A i₀ a = 1) :
    ∃ k : ℕ, k ≤ (activeSupport p).card -
        (A.submatrix id (fun a : activeSupport p => (a : α))).rank ∧
      ∃ path : Fin (k + 1) → (α → ℝ),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        feasibleLaw A b (path (Fin.last k)) ∧
        LinearIndependent ℝ
          (A.submatrix id (fun a : activeSupport (path (Fin.last k)) => (a : α))).col := by
  classical
  let D := fun p : α → ℝ => (activeSupport p).card -
    (A.submatrix id (fun a : activeSupport p => (a : α))).rank
  have h : ∀ m : ℕ, ∀ p : α → ℝ, D p = m → feasibleLaw A b p →
      ∃ k : ℕ, k ≤ D p ∧ ∃ path : Fin (k + 1) → (α → ℝ),
        path ⟨0, Nat.zero_lt_succ k⟩ = p ∧
        (∀ j : Fin k, reductionStep A b (path j.castSucc) (path j.succ)) ∧
        feasibleLaw A b (path (Fin.last k)) ∧
        LinearIndependent ℝ
          (A.submatrix id (fun a : activeSupport (path (Fin.last k)) => (a : α))).col := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro p hD hp
      by_cases hlin : LinearIndependent ℝ
          (A.submatrix id (fun a : activeSupport p => (a : α))).col
      · refine ⟨0, Nat.zero_le _, fun _ => p, rfl, ?_, hp, hlin⟩
        intro j
        exact Fin.elim0 j
      · obtain ⟨q, hq, hmq, hAq, hCq, hsubq, hcardq, horientationq⟩ :=
          active_support_deletion A b p hp.1 hp.2.1 hp.2.2 i₀ hconstant hlin
        have hdim : D q < D p := support_dimension_strict_drop A p q
          (hp.2.2.trans hAq.symm) hsubq hcardq
        have hfeasibleq : feasibleLaw A b q := ⟨hq, hmq, hAq⟩
        obtain ⟨k, hk, path, hfirst, hsteps, hlast, hlinlast⟩ :=
          ih (D q) (by omega) q rfl hfeasibleq
        let path' : Fin (k + 1 + 1) → (α → ℝ) := Fin.cases p path
        have hlast' : path' (Fin.last (k + 1)) = path (Fin.last k) := rfl
        refine ⟨k + 1, by omega, path', rfl, ?_, ?_, ?_⟩
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · have hstep : reductionStep A b p q :=
              ⟨hfeasibleq, hCq, hsubq, hcardq, horientationq⟩
            change reductionStep A b p (path ⟨0, Nat.zero_lt_succ k⟩)
            rw [hfirst]
            exact hstep
          · exact hsteps j
        · rwa [hlast']
        · rwa [hlast']
  exact h (D p) p rfl hp

end EntropyDesigns
