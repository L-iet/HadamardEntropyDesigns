/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0.
Catalan-shell array construction is prior work; see the paper attribution. -/
module
public import EntropyPermutationCost.CatalanShellSymmetry
public import EntropyPermutationCost.BooleanCountMoments
public import EntropyPermutationCost.CentralBinomialLower
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
@[expose] public section
namespace EntropyDesigns.PermutationCost
open scoped BigOperators

 theorem catalan_shell_sign_moments (k : ℕ) (hk : 1≤k) :
    (∀ i : Fin (2*k+1),(∑ r : CatalanShellIndex k,bitSign (catalanShellRows k r i))=0) ∧
    (∀ i j : Fin (2*k+1),i≠j → (∑ r : CatalanShellIndex k,
      bitSign (catalanShellRows k r i)*bitSign (catalanShellRows k r j))=0) := by
  have hone (i : Fin (2*k+1)) :
      2*(Finset.univ.filter (fun r : CatalanShellIndex k => catalanShellRows k r i=true)).card=
        Fintype.card (CatalanShellIndex k) := by
    rw [catalan_shell_one_count,catalan_shell_index_card]
  constructor
  · intro i
    exact boolean_sign_sum_from_true_count _ (hone i)
  · intro i j hij
    apply boolean_pair_sign_sum_from_counts _ _ (hone i) (hone j)
    rw [catalan_shell_index_card]
    have hh := catalan_shell_two_count k hk i j hij
    omega

 theorem symmetric_strength_two_catalan_array (d : ℕ) (hd : 2≤d) :
    ∃ rows : Fin (2*Nat.centralBinom (d/2)) → Fin d → Bool,
      IsBinaryStrengthTwo rows ∧ IsFullyPermutationSymmetric rows := by
  classical
  let k := d/2
  have hk : 1≤k := by dsimp [k];omega
  have hdim : d≤2*k+1 := by dsimp [k];omega
  let col : Fin d ↪ Fin (2*k+1) := Fin.castLEEmb hdim
  let e : Fin (2*Nat.centralBinom k) ≃ CatalanShellIndex k :=
    (Fintype.equivFinOfCardEq (catalan_shell_index_card k)).symm
  let rows : Fin (2*Nat.centralBinom k) → Fin d → Bool :=
    fun r i => catalanShellRows k (e r) (col i)
  have hm := catalan_shell_sign_moments k hk
  have hf (i : Fin d) : (∑ r,bitSign (rows r i))=0 := by
    exact (Equiv.sum_comp e (fun a => bitSign (catalanShellRows k a (col i)))).trans (hm.1 (col i))
  have hp (i j : Fin d) (hij : i≠j) :
      (∑ r,bitSign (rows r i)*bitSign (rows r j))=0 := by
    exact (Equiv.sum_comp e (fun a => bitSign (catalanShellRows k a (col i))*
      bitSign (catalanShellRows k a (col j)))).trans
        (hm.2 (col i) (col j) (fun h => hij (col.injective h)))
  refine ⟨rows,sign_moments_strength_two rows hf hp,?_⟩
  apply row_permutations_imply_full_symmetry
  exact row_permutations_restrict (fun r i => catalanShellRows k (e r) i) col
    (catalan_shell_reindex_row_permutations k _ e)

 def IsSymmetricStrengthTwoRunCount (d N : ℕ) : Prop :=
  0<N ∧ ∃ rows : Fin N → Fin d → Bool,
    IsBinaryStrengthTwo rows ∧ IsFullyPermutationSymmetric rows

noncomputable def symmetricRunCount (d : ℕ) : ℕ :=
  sInf {N : ℕ | IsSymmetricStrengthTwoRunCount d N}

 theorem symmetric_run_count_set_nonempty {d : ℕ} (hd : 2≤d) :
    {N : ℕ | IsSymmetricStrengthTwoRunCount d N}.Nonempty := by
  obtain ⟨rows,ho,hs⟩ := symmetric_strength_two_catalan_array d hd
  exact ⟨2*Nat.centralBinom (d/2),Nat.mul_pos (by decide) (Nat.centralBinom_pos _),rows,ho,hs⟩

 theorem symmetric_run_count_realized {d : ℕ} (hd : 2≤d) :
    IsSymmetricStrengthTwoRunCount d (symmetricRunCount d) :=
  Nat.sInf_mem (symmetric_run_count_set_nonempty hd)

 theorem symmetric_run_count_exact_bounds {d : ℕ} (hd : 2≤d) :
    d.choose (leastCentralWeight d)≤symmetricRunCount d ∧
      symmetricRunCount d≤2*Nat.centralBinom (d/2) := by
  obtain ⟨hn,rows,hOA,hsym⟩ := symmetric_run_count_realized hd
  refine ⟨symmetric_strength_two_exact_binomial_lower hd hn rows hOA hsym,?_⟩
  obtain ⟨rows,hOA,hsym⟩ := symmetric_strength_two_catalan_array d hd
  exact Nat.sInf_le ⟨Nat.mul_pos (by decide) (Nat.centralBinom_pos _),rows,hOA,hsym⟩

end EntropyDesigns.PermutationCost
