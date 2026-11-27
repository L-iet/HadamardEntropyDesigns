/- Copyright (c) 2026 Joshua Mark. Released under Apache 2.0. -/
module
public import EntropySupportDistance.FiniteSetMatching
@[expose] public section
set_option maxHeartbeats 1500000
namespace EntropyDesigns.SupportFace
noncomputable section

theorem matching_changed_card {A : Type*} [DecidableEq A] (S T : Finset A)
    (E : {x // x∈S} ≃ {y // y∈T})
    (hfix : ∀ x,(E x).val=x.val ↔ x.val∈T) :
    Fintype.card {x : {x // x∈S} // (E x).val≠x.val}=S.card-(S∩T).card := by
  classical
  let Q : {x : {x // x∈S} // (E x).val≠x.val} ≃ {x // x∈S\T} :=
    { toFun := fun x => ⟨x.val.val,Finset.mem_sdiff.mpr ⟨x.val.property,by
        intro hx
        exact x.property ((hfix x.val).mpr hx)⟩⟩
      invFun := fun x => ⟨⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩,by
        intro hx
        exact (Finset.mem_sdiff.mp x.property).2
          ((hfix ⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩).mp hx)⟩
      left_inv := fun x => by apply Subtype.ext;apply Subtype.ext;rfl
      right_inv := fun x => by apply Subtype.ext;rfl }
  have hc := Fintype.card_congr Q
  simpa only [Fintype.card_coe,Finset.card_sdiff,Finset.inter_comm] using hc

theorem finite_sets_exact_replacements {A : Type*} [DecidableEq A] (S T : Finset A)
    (hcard : S.card=T.card) :
    ∃ E : {x // x∈S} ≃ {y // y∈T},
      (∀ x,(E x).val=x.val ↔ x.val∈T) ∧
      Fintype.card {x : {x // x∈S} // (E x).val≠x.val}=S.card-(S∩T).card := by
  obtain ⟨E,hfix⟩ := finite_sets_matching S T hcard
  exact ⟨E,hfix,matching_changed_card S T E hfix⟩

theorem every_matching_replacements_ge {A : Type*} [DecidableEq A] (S T : Finset A)
    (f : {x // x∈S} → {y // y∈T}) :
    S.card-(S∩T).card≤Fintype.card {x : {x // x∈S} // (f x).val≠x.val} := by
  classical
  let g : {x // x∈S\T} → {x : {x // x∈S} // (f x).val≠x.val} := fun x =>
    ⟨⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩,by
      intro h
      have hy := (f ⟨x.val,(Finset.mem_sdiff.mp x.property).1⟩).property
      rw [h] at hy
      exact (Finset.mem_sdiff.mp x.property).2 hy⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x : {x // x∈S} // (f x).val≠x.val} => z.val.val) h
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe,Finset.card_sdiff,Finset.inter_comm] using hc

end
end EntropyDesigns.SupportFace
