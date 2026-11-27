/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.ExchangePaths
public import EntropySeedRepair.TruthTransfer
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section
variable {α δ : Type*} [Fintype α] [DecidableEq α] [DecidableEq δ]

def TruthExchangePathWith (P : Finset α → (α → δ) → Prop) :
    ℕ → Finset α → (α → δ) → Finset α → (α → δ) → Prop
  | 0,T,rows,U,finalRows => T=U ∧ rows=finalRows ∧ P T rows
  | n+1,T,rows,U,finalRows => P T rows ∧
      ∃ a∈T,∃ b∉T,TruthExchangePathWith P n (insert b (T.erase a))
        (fun z => rows (Equiv.swap a b z)) U finalRows

theorem one_exchange_complement (T : Finset α) (a b : α) (ha : a∈T) (hb : b∉T) :
    (insert b (T.erase a))ᶜ=insert a ((Tᶜ).erase b) := by
  have hab : a≠b := by intro h; apply hb; simpa [h] using ha
  ext x
  by_cases hxa : x=a
  · subst x
    simp [hab,Ne.symm hab]
  · by_cases hxb : x=b
    · subst x
      simp [hab,Ne.symm hab]
    · simp [hxa,hxb]

theorem one_exchange_complement_truth_law (T : Finset α) (a b : α)
    (ha : a∈T) (hb : b∉T) (rows : α → δ) :
    uniformSupportTruthLaw ((insert b (T.erase a))ᶜ) (fun z => rows (Equiv.swap a b z))=
      uniformSupportTruthLaw (Tᶜ) rows := by
  rw [one_exchange_complement T a b ha hb]
  apply one_exchange_truth_law_preserved
  · simpa using ha
  · simpa using hb

theorem lift_exchange_path_with_invariant (P : Finset α → (α → δ) → Prop)
    {k : ℕ} (T U : Finset α) (hpath : SupportExchangePath k T U) (rows : α → δ)
    (hP : ∀ V : Finset α,V.card=T.card → ∀ newRows : α → δ,P V newRows) :
    ∃ finalRows : α → δ,TruthExchangePathWith P k T rows U finalRows ∧
      uniformSupportTruthLaw (Uᶜ) finalRows=uniformSupportTruthLaw (Tᶜ) rows := by
  induction k generalizing T rows with
  | zero =>
      change T=U at hpath
      subst U
      exact ⟨rows,⟨rfl,rfl,hP T rfl rows⟩,rfl⟩
  | succ k ih =>
      obtain ⟨C,hTC,hCU⟩ := hpath
      obtain ⟨a,ha,b,hb,rfl⟩ := hTC
      let newRows : α → δ := fun z => rows (Equiv.swap a b z)
      have hcard : (insert b (T.erase a)).card=T.card :=
        one_exchange_preserves_card T _ ⟨a,ha,b,hb,rfl⟩
      have hP' : ∀ V : Finset α,V.card=(insert b (T.erase a)).card →
          ∀ nr : α → δ,P V nr := by
        intro V hV nr
        exact hP V (hV.trans hcard) nr
      obtain ⟨finalRows,htrace,hlaw⟩ := ih (T:=insert b (T.erase a)) (rows:=newRows) hCU hP'
      refine ⟨finalRows,⟨hP T rfl rows,a,ha,b,hb,htrace⟩,?_⟩
      exact hlaw.trans (one_exchange_complement_truth_law T a b ha hb rows)

theorem truth_exchange_path_underlying (P : Finset α → (α → δ) → Prop)
    {k : ℕ} (T U : Finset α) (rows finalRows : α → δ)
    (h : TruthExchangePathWith P k T rows U finalRows) : SupportExchangePath k T U := by
  induction k generalizing T rows with
  | zero => exact h.1
  | succ k ih =>
      obtain ⟨_,a,ha,b,hb,htail⟩ := h
      exact ⟨insert b (T.erase a),⟨a,ha,b,hb,rfl⟩,ih _ _ htail⟩


theorem lift_exchange_path_with_law_invariant (P : Finset α → (α → δ) → Prop)
    (law : δ → ℝ) {k : ℕ} (T U : Finset α) (hpath : SupportExchangePath k T U)
    (rows : α → δ) (hlaw : uniformSupportTruthLaw (Tᶜ) rows=law)
    (hP : ∀ V : Finset α,V.card=T.card → ∀ newRows : α → δ,P V newRows) :
    ∃ finalRows : α → δ,TruthExchangePathWith
      (fun V nr => P V nr ∧ uniformSupportTruthLaw (Vᶜ) nr=law) k T rows U finalRows := by
  induction k generalizing T rows with
  | zero =>
      change T=U at hpath
      subst U
      exact ⟨rows,⟨rfl,rfl,hP T rfl rows,hlaw⟩⟩
  | succ k ih =>
      obtain ⟨C,hTC,hCU⟩ := hpath
      obtain ⟨a,ha,b,hb,rfl⟩ := hTC
      let newRows : α → δ := fun z => rows (Equiv.swap a b z)
      have hcard : (insert b (T.erase a)).card=T.card :=
        one_exchange_preserves_card T _ ⟨a,ha,b,hb,rfl⟩
      have hP' : ∀ V : Finset α,V.card=(insert b (T.erase a)).card →
          ∀ nr : α → δ,P V nr := by
        intro V hV nr
        exact hP V (hV.trans hcard) nr
      have hnewlaw : uniformSupportTruthLaw ((insert b (T.erase a))ᶜ) newRows=law :=
        (one_exchange_complement_truth_law T a b ha hb rows).trans hlaw
      obtain ⟨finalRows,htrace⟩ := ih (T:=insert b (T.erase a)) (rows:=newRows) hCU hnewlaw hP'
      exact ⟨finalRows,⟨⟨hP T rfl rows,hlaw⟩,a,ha,b,hb,htrace⟩⟩

theorem truth_exchange_path_final_invariant (P : Finset α → (α → δ) → Prop)
    {k : ℕ} (T U : Finset α) (rows finalRows : α → δ)
    (h : TruthExchangePathWith P k T rows U finalRows) : P U finalRows := by
  induction k generalizing T rows with
  | zero =>
      obtain ⟨rfl,rfl,hP⟩ := h
      exact hP
  | succ k ih =>
      obtain ⟨_,a,ha,b,hb,htail⟩ := h
      exact ih _ _ htail

end
end EntropyDesigns.SupportRepair
