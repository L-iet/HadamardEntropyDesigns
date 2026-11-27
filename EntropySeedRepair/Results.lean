/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySeedRepair.BooleanRepair
public import EntropySeedRepair.TruthPaths
@[expose] public section
namespace EntropyDesigns.SupportRepair
noncomputable section

def HasTruthDegree {r d : ℕ} (D : ℕ) (T : Finset (Finset (Fin r)))
    (rows : Finset (Fin r) → Fin d → Bool) : Prop :=
  ∃ f : Fin d → (Finset (Fin r) → ZMod 2),
    (∀ i,f i∈lowDegreeBooleanCode r D) ∧
    (∀ i z,z∉T → f i z=if rows z i then 1 else 0)

theorem proper_complement_of_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    (V : Finset α) (hV : V.Nonempty) : Vᶜ≠Finset.univ := by
  intro he
  obtain ⟨z,hz⟩ := hV
  have hc : z∈Vᶜ := by rw [he]; simp
  exact (Finset.mem_compl.mp hc) hz

theorem complement_range_as_image {r : ℕ} (U : Finset (Finset (Fin r))) :
    Set.range (fun z : {z : Finset (Fin r) // z∉Uᶜ} => booleanSupportVector z.val)=
      booleanSupportVector '' (U : Set (Finset (Fin r))) := by
  classical
  ext v
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z.val,by simpa using z.property,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨⟨z,by simpa using hz⟩,rfl⟩

theorem minimum_support_exchanges {r d : ℕ} (hr : 2≤r)
    (T : Finset (Finset (Fin r))) (hcard : r+1≤T.card)
    (rows : Finset (Fin r) → Fin d → Bool) :
    ∃ (U : Finset (Finset (Fin r))) (finalRows : Finset (Fin r) → Fin d → Bool),
      U.card=T.card ∧
      affineSpan (ZMod 2) (booleanSupportVector '' (U : Set (Finset (Fin r))))=⊤ ∧
      TruthExchangePathWith
        (fun V nr => HasTruthDegree (r-1) V nr ∧
          uniformSupportTruthLaw (Vᶜ) nr=uniformSupportTruthLaw (Tᶜ) rows)
        (labelAffineCodimension T) T rows U finalRows ∧
      HasTruthDegree (r-2) U finalRows ∧
      uniformSupportTruthLaw (Uᶜ) finalRows=uniformSupportTruthLaw (Tᶜ) rows ∧
      (∀ k W,SupportExchangePath k T W →
        affineSpan (ZMod 2) (booleanSupportVector '' (W : Set (Finset (Fin r))))=⊤ →
          labelAffineCodimension T≤k) := by
  classical
  obtain ⟨U,hUcard,hUspan,hpath⟩ := boolean_support_repair_at_codimension T hcard
  have hP : ∀ V : Finset (Finset (Fin r)),V.card=T.card →
      ∀ nr : Finset (Fin r) → Fin d → Bool,HasTruthDegree (r-1) V nr := by
    intro V hV nr
    have hne : V.Nonempty := Finset.card_pos.mp (by omega)
    have hp := proper_complement_of_nonempty V hne
    obtain ⟨f,hf,hm⟩ := proper_support_truth_extension (by omega : 0<r) (Vᶜ) hp nr
    exact ⟨f,hf,fun i z hz => hm i z (Finset.mem_compl.mpr hz)⟩
  obtain ⟨finalRows,htrace⟩ := lift_exchange_path_with_law_invariant
    (fun V nr => HasTruthDegree (r-1) V nr) (uniformSupportTruthLaw (Tᶜ) rows)
    T U hpath rows rfl hP
  have hfinal := truth_exchange_path_final_invariant
    (fun V nr => HasTruthDegree (r-1) V nr ∧
      uniformSupportTruthLaw (Vᶜ) nr=uniformSupportTruthLaw (Tᶜ) rows)
    T U rows finalRows htrace
  have hUproper := proper_complement_of_nonempty U
    (Finset.card_pos.mp (by omega : 0<U.card))
  have hspan : affineSpan (ZMod 2) (Set.range
      (fun z : {z : Finset (Fin r) // z∉Uᶜ} => booleanSupportVector z.val))=⊤ := by
    rw [complement_range_as_image]
    exact hUspan
  obtain ⟨f,hf,hm⟩ := spanning_complement_truth_extension hr (Uᶜ) hUproper hspan finalRows
  refine ⟨U,finalRows,hUcard,hUspan,htrace,⟨f,hf,?_⟩,hfinal.2,?_⟩
  · intro i z hz
    exact hm i z (Finset.mem_compl.mpr hz)
  · intro k W hp hs
    exact boolean_support_exchange_lower T W hcard hp hs

end
end EntropyDesigns.SupportRepair
