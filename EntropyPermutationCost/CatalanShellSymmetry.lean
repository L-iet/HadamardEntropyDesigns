/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPermutationCost.CatalanShellIncidence
public import EntropyPermutationCost.PermutationLayers
public import Mathlib.Logic.Equiv.Fintype
@[expose] public section
namespace EntropyDesigns.PermutationCost

noncomputable def catalanShellRowPerm (k : ℕ) (σ : Equiv.Perm (Fin (2*k+1))) :
    Equiv.Perm (CatalanShellIndex k) :=
  Equiv.sumCongr (Equiv.refl _) ((Equiv.finsetCongr σ.symm).subtypeEquiv
    (by intro s;simp [Equiv.finsetCongr_apply]))

 theorem catalan_shell_row_perm_apply (k : ℕ) (σ : Equiv.Perm (Fin (2*k+1)))
    (r : CatalanShellIndex k) (i : Fin (2*k+1)) :
    catalanShellRows k (catalanShellRowPerm k σ r) i=catalanShellRows k r (σ i) := by
  cases r with
  | inl a => rfl
  | inr s =>
    change decide (i∈s.val.map σ.symm.toEmbedding)=decide (σ i∈s.val)
    simp

 theorem row_permutation_preserves_pattern_count {α : Type*} [Fintype α]
    {d : ℕ} (rows : α → Fin d → Bool) (σ : Equiv.Perm (Fin d))
    (E : Equiv.Perm α) (hE : ∀ r i,rows (E r) i=rows r (σ i)) (x : Fin d → Bool) :
    (Finset.univ.filter (fun r => rows r=fun i => x (σ i))).card=
      (Finset.univ.filter (fun r => rows r=x)).card := by
  classical
  have he (r : α) : rows r=x ↔ rows (E r)=fun i => x (σ i) := by
    constructor
    · intro h
      funext i
      rw [hE,h]
    · intro h
      funext i
      obtain ⟨j,rfl⟩ := σ.surjective i
      exact (hE r j).symm.trans (congrFun h j)
  simpa only [Fintype.subtype_card] using
    (Fintype.card_congr (E.subtypeEquiv (p := fun r => rows r=x)
      (q := fun r => rows r=fun i => x (σ i)) he)).symm

 theorem row_permutations_imply_full_symmetry {N d : ℕ}
    (rows : Fin N → Fin d → Bool)
    (hperm : ∀ σ : Equiv.Perm (Fin d),∃ E : Equiv.Perm (Fin N),
      ∀ r i,rows (E r) i=rows r (σ i)) : IsFullyPermutationSymmetric rows := by
  intro σ x
  obtain ⟨E,hE⟩ := hperm σ
  exact row_permutation_preserves_pattern_count rows σ E hE x

 theorem catalan_shell_reindex_row_permutations (k N : ℕ)
    (e : Fin N ≃ CatalanShellIndex k) (σ : Equiv.Perm (Fin (2*k+1))) :
    ∃ E : Equiv.Perm (Fin N),∀ r i,
      catalanShellRows k (e (E r)) i=catalanShellRows k (e r) (σ i) := by
  let E := (e.trans (catalanShellRowPerm k σ)).trans e.symm
  refine ⟨E,fun r i => ?_⟩
  simpa only [E,Equiv.trans_apply,Equiv.apply_symm_apply] using
    catalan_shell_row_perm_apply k σ (e r) i

 theorem row_permutations_restrict {N d D : ℕ}
    (rows : Fin N → Fin D → Bool) (e : Fin d ↪ Fin D)
    (hperm : ∀ σ : Equiv.Perm (Fin D),∃ E : Equiv.Perm (Fin N),
      ∀ r i,rows (E r) i=rows r (σ i)) :
    ∀ σ : Equiv.Perm (Fin d),∃ E : Equiv.Perm (Fin N),
      ∀ r i,rows (E r) (e i)=rows r (e (σ i)) := by
  classical
  intro σ
  obtain ⟨E,hE⟩ := hperm (σ.viaFintypeEmbedding e)
  refine ⟨E,fun r i => ?_⟩
  simpa only [Equiv.Perm.viaFintypeEmbedding_apply_image] using hE r (e i)

end EntropyDesigns.PermutationCost
