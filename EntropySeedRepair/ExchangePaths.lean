/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.BasisSubset
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section
variable {α : Type*} [DecidableEq α]

def OneSupportExchange (S T : Finset α) : Prop :=
  ∃ a∈S,∃ b∉S,T=insert b (S.erase a)

def SupportExchangePath : ℕ → Finset α → Finset α → Prop
  | 0,S,T => S=T
  | n+1,S,T => ∃ U,OneSupportExchange S U ∧ SupportExchangePath n U T

theorem support_difference_triangle (A B C : Finset α) :
    (A\B).card≤(A\C).card+(C\B).card := by
  have hsub : A\B⊆(A\C)∪(C\B) := by
    intro x hx
    obtain ⟨hxA,hxnotB⟩ := Finset.mem_sdiff.mp hx
    by_cases hxC : x∈C
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxC,hxnotB⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxA,hxC⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem one_exchange_difference_le_one (A C : Finset α) (h : OneSupportExchange A C) :
    (A\C).card≤1 := by
  obtain ⟨a,ha,b,hb,rfl⟩ := h
  have hsub : A\insert b (A.erase a)⊆{a} := by
    intro x hx
    obtain ⟨hxA,hxnotC⟩ := Finset.mem_sdiff.mp hx
    apply Finset.mem_singleton.mpr
    by_contra hxa
    exact hxnotC (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxa,hxA⟩))
  have hc := Finset.card_le_card hsub
  simpa using hc

theorem one_exchange_preserves_card (A C : Finset α) (h : OneSupportExchange A C) : C.card=A.card := by
  obtain ⟨a,ha,b,hb,rfl⟩ := h
  have hbe : b∉A.erase a := fun he => hb (Finset.mem_of_mem_erase he)
  have hpos : 0<A.card := Finset.card_pos.mpr ⟨a,ha⟩
  rw [Finset.card_insert_of_notMem hbe,Finset.card_erase_of_mem ha]
  omega

theorem exchange_path_difference_bound {k : ℕ} (A B : Finset α)
    (h : SupportExchangePath k A B) : (A\B).card≤k := by
  induction k generalizing A with
  | zero =>
      change A=B at h
      subst B
      simp
  | succ k ih =>
      obtain ⟨C,hAC,hCB⟩ := h
      have ht := support_difference_triangle A B C
      have ho := one_exchange_difference_le_one A C hAC
      have hr := ih C hCB
      omega

theorem exchange_path_preserves_card {k : ℕ} (A B : Finset α)
    (h : SupportExchangePath k A B) : B.card=A.card := by
  induction k generalizing A with
  | zero =>
      change A=B at h
      rw [h]
  | succ k ih =>
      obtain ⟨C,hAC,hCB⟩ := h
      exact (ih C hCB).trans (one_exchange_preserves_card A C hAC)

theorem exists_shortest_exchange_path (A B : Finset α) (hcard : A.card=B.card) :
    SupportExchangePath (A\B).card A B := by
  suffices h : ∀ d,∀ A : Finset α,A.card=B.card → (A\B).card=d → SupportExchangePath d A B by
    exact h _ A hcard rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro A hc hd
      by_cases hzero : d=0
      · have hsub : A⊆B := by
          intro x hxA
          by_contra hxnotB
          have hp : 0<(A\B).card := Finset.card_pos.mpr ⟨x,Finset.mem_sdiff.mpr ⟨hxA,hxnotB⟩⟩
          omega
        have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
        simpa [SupportExchangePath,hzero] using heq
      · have hdpos : 0<d := by omega
        obtain ⟨a,haDiff⟩ := Finset.card_pos.mp (by omega : 0<(A\B).card)
        obtain ⟨haA,hanotB⟩ := Finset.mem_sdiff.mp haDiff
        have hdiff : (B\A).card=(A\B).card := by
          simp only [Finset.card_sdiff,hc,Finset.inter_comm]
        obtain ⟨b,hbDiff⟩ := Finset.card_pos.mp (by omega : 0<(B\A).card)
        obtain ⟨hbB,hbnotA⟩ := Finset.mem_sdiff.mp hbDiff
        let C := insert b (A.erase a)
        have hstep : OneSupportExchange A C := ⟨a,haA,b,hbnotA,rfl⟩
        have hCcard : C.card=B.card := (one_exchange_preserves_card A C hstep).trans hc
        have hset : C\B=(A\B).erase a := by
          ext x
          simp only [C,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_erase]
          constructor
          · rintro ⟨hx,hxnotB⟩
            rcases hx with hxb|⟨hxne,hxA⟩
            · exact False.elim (hxnotB (by simpa [hxb] using hbB))
            · exact ⟨hxne,hxA,hxnotB⟩
          · rintro ⟨hxne,hxA,hxnotB⟩
            exact ⟨Or.inr ⟨hxne,hxA⟩,hxnotB⟩
        have hCd : (C\B).card=d-1 := by
          rw [hset,Finset.card_erase_of_mem haDiff,hd]
        have hrec := ih (d-1) (by omega) C hCcard hCd
        have heq : d=(d-1)+1 := by omega
        rw [heq]
        exact ⟨C,hstep,hrec⟩

end
end EntropyDesigns.SupportRepair
