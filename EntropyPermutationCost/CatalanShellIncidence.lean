/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropyPermutationCost.CatalanShellCard
@[expose] public section
namespace EntropyDesigns.PermutationCost

def catalanShellRows (k : ℕ) : CatalanShellIndex k → Fin (2*k+1) → Bool
  | Sum.inl _, _ => false
  | Sum.inr s, i => decide (i∈s.val)

def catalanShellSupport (k : ℕ) : CatalanShellIndex k → Finset (Fin (2*k+1))
  | Sum.inl _ => ∅
  | Sum.inr s => s.val

 theorem catalan_shell_incidence_count (k : ℕ) (t : Finset (Fin (2*k+1)))
    (ht : t.Nonempty) (hsize : t.card≤k+1) :
    (Finset.univ.filter (fun r : CatalanShellIndex k =>
      ∀ i,i∈t → catalanShellRows k r i=true)).card=
      (2*k+1-t.card).choose (k+1-t.card) := by
  classical
  let U := Finset.univ.filter (fun r : CatalanShellIndex k =>
    ∀ i,i∈t → catalanShellRows k r i=true)
  let V := (Finset.univ.powersetCard (k+1)).filter (t⊆·)
  have hinr (r : CatalanShellIndex k) (hr : r∈U) :
      ∃ s : {s : Finset (Fin (2*k+1)) // s.card=k+1},r=Sum.inr s := by
    cases r with
    | inl a =>
      obtain ⟨i,hi⟩ := ht
      have hh := (Finset.mem_filter.mp hr).2 i hi
      simp [catalanShellRows] at hh
    | inr s => exact ⟨s,rfl⟩
  calc
    _=V.card := by
      apply Finset.card_bij (fun r _ => catalanShellSupport k r)
      · intro r hr
        obtain ⟨s,rfl⟩ := hinr r hr
        have hsub : t⊆s.val := by
          intro i hi
          have hh := (Finset.mem_filter.mp hr).2 i hi
          simpa [catalanShellRows] using hh
        simpa [V,catalanShellSupport,Finset.mem_powersetCard,s.property] using hsub
      · intro r hr s hs he
        obtain ⟨a,rfl⟩ := hinr r hr
        obtain ⟨b,rfl⟩ := hinr s hs
        exact congrArg Sum.inr (Subtype.ext he)
      · intro s hs
        have hc : s.card=k+1 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
        refine ⟨Sum.inr ⟨s,hc⟩,?_,rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro i hi
        simpa [catalanShellRows] using (Finset.mem_filter.mp hs).2 hi
    _=_ := by
      simpa only [V,Finset.card_univ,Fintype.card_fin] using
        Finset.card_filter_powersetCard_subset t Finset.univ (k+1)
          (Finset.subset_univ _) hsize

 theorem catalan_shell_one_count (k : ℕ) (i : Fin (2*k+1)) :
    (Finset.univ.filter (fun r : CatalanShellIndex k => catalanShellRows k r i=true)).card=
      Nat.centralBinom k := by
  have hh := catalan_shell_incidence_count k {i} (by simp) (by simp)
  simpa [Nat.centralBinom] using hh

 theorem catalan_shell_two_count (k : ℕ) (hk : 1≤k)
    (i j : Fin (2*k+1)) (hij : i≠j) :
    2*(Finset.univ.filter (fun r : CatalanShellIndex k =>
      catalanShellRows k r i=true ∧ catalanShellRows k r j=true)).card=
        Nat.centralBinom k := by
  have hh := catalan_shell_incidence_count k {i,j} (by simp) (by simp [hij];omega)
  have he : (2*k+1-2)=2*k-1 := by omega
  have hf : k+1-2=k-1 := by omega
  have hb : (Finset.univ.filter (fun r : CatalanShellIndex k =>
      catalanShellRows k r i=true ∧ catalanShellRows k r j=true)).card=
      (2*k-1).choose (k-1) := by
    simpa [hij,he,hf] using hh
  rw [hb]
  exact middle_shell_double_pair_count k hk

end EntropyDesigns.PermutationCost
