/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyCubic.Character
@[expose] public section
namespace EntropyDesigns
noncomputable section
open scoped BigOperators symmDiff

theorem degree_one_boolean_parallelogram {r : ℕ} (g : Finset (Fin r) → ZMod 2)
    (hg : g∈lowDegreeBooleanCode r 1) (A B : Finset (Fin r)) :
    g (A∆B)+g ∅=g A+g B := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨s,rfl⟩ := hg
    by_cases hs : s.val=∅
    · simp [hs,squarefreeBooleanMonomial]
    · obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have he : s.val={i} := by
        ext j
        simp only [Finset.mem_singleton]
        constructor
        · intro hj
          exact Finset.card_le_one.mp s.property j hj i hi
        · intro hj; subst j; exact hi
      by_cases hA : i∈A <;> by_cases hB : i∈B <;>
        norm_num [he,squarefreeBooleanMonomial,Finset.mem_symmDiff,hA,hB] <;> decide
  | zero => simp
  | add f g hf hg ihf ihg =>
    change (f (A∆B)+g (A∆B))+(f ∅+g ∅)=(f A+g A)+(f B+g B)
    linear_combination ihf+ihg
  | smul c f hf ih =>
    change c*f (A∆B)+c*f ∅=c*f A+c*f B
    linear_combination c*ih

theorem boolean_parallelogram_violation_not_affine {r : ℕ} (g : Finset (Fin r) → ZMod 2)
    (A B : Finset (Fin r)) (h : g (A∆B)+g ∅≠g A+g B) :
    g∉lowDegreeBooleanCode r 1 := by
  intro hg
  exact h (degree_one_boolean_parallelogram g hg A B)

def squarefreeBooleanPolynomial {r : ℕ} (terms : Finset (Finset (Fin r)))
    (z : Finset (Fin r)) : ZMod 2 := ∑ s∈terms,squarefreeBooleanMonomial s z

theorem squarefreeBooleanPolynomial_mem {r d : ℕ} (terms : Finset (Finset (Fin r)))
    (hdegree : ∀ s∈terms,s.card≤d) : squarefreeBooleanPolynomial terms∈lowDegreeBooleanCode r d := by
  classical
  have heq : squarefreeBooleanPolynomial terms=(∑ s∈terms,squarefreeBooleanMonomial s) := by
    funext z
    simp only [squarefreeBooleanPolynomial,Finset.sum_apply]
  rw [heq]
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.subset_span
  exact ⟨⟨s,hdegree s hs⟩,rfl⟩

def naturalMaskSupport (r mask : ℕ) : Finset (Fin r) :=
  Finset.univ.filter (fun i => Nat.testBit mask i.val)

def polynomialMaskTerms (r : ℕ) (masks : List ℕ) : Finset (Finset (Fin r)) :=
  (masks.map (naturalMaskSupport r)).toFinset

end
end EntropyDesigns
